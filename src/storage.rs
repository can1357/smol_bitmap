//! Internal storage representation and management for the bitmap.

use alloc::{boxed::Box, vec, vec::Vec};
use core::{
    borrow::Borrow,
    mem,
    ops::{Deref, DerefMut, Index, IndexMut},
    ptr, slice,
};

/// Number of 64-bit words that can be stored inline
pub(crate) const WORDS_INLINE: usize = 2;
pub(crate) const WORDS_MINEXT: usize = 4;
pub(crate) const BITS_INLINE: usize = 64 * WORDS_INLINE - 1;

/// Convert bit index to (word index, bit position within word)
#[inline(always)]
pub(crate) const fn bitpos(idx: usize) -> (usize, usize) {
    (idx >> 6, idx & 63)
}

/// Checks if a word has its most significant bit set.
#[inline(always)]
pub(crate) const fn msb(val: u64) -> bool {
    val.cast_signed() < 0
}

pub(crate) type ArrayBitmap = [u64; WORDS_INLINE];

/// Attempts to pack words into inline storage.
/// Returns Some(array) if the words can fit inline, None otherwise.
/// Words can fit inline if:
/// 1. There are at most INLINE_QWORDS non-zero words
/// 2. The last word has its MSB clear (to distinguish from external storage)
/// 3. The actual bits used don't exceed INLINE_CAPACITY
#[inline(always)]
pub(crate) fn try_inline(words: impl AsRef<[u64]>) -> Option<ArrayBitmap> {
    let words = words.as_ref();
    if words.len() <= WORDS_INLINE {
        if let Ok(array) = <ArrayBitmap>::try_from(words)
            && msb(array[WORDS_INLINE - 1])
        {
            return None;
        }
        let mut array = [0; WORDS_INLINE];
        // SAFETY: We've verified that words.len() <= WORDS_INLINE above,
        // so copying words.len() elements into array is safe.
        unsafe {
            ptr::copy_nonoverlapping(words.as_ptr(), array.as_mut_ptr(), words.len());
        }
        return Some(array);
    }
    None
}

/// Promotes an inline bitmap to a heap-allocated vector.
///
/// This function is called when inline storage can't be used due to MSB
/// constraints (e.g., when the highest inline bit is set). It creates a vector
/// with minimum external capacity to avoid immediate reallocation.
///
/// # Performance Note
/// Creates an intermediate array to ensure MIN_EXTERNAL capacity, which avoids
/// the allocation churn that would happen with capacity == INLINE_QWORDS.
#[inline(always)]
pub(crate) fn inline_promote(words: &[u64; WORDS_INLINE]) -> Vec<u64> {
    let mut ext = [0; WORDS_MINEXT];
    ext[..WORDS_INLINE].copy_from_slice(words);
    ext.to_vec()
}

/// Removes trailing zero words from a slice.
/// This is used to normalize the representation and save space.
#[inline(always)]
pub(crate) const fn rtrim0(mut slice: &[u64]) -> &[u64] {
    while let [rest @ .., 0] = slice {
        slice = rest;
    }
    slice
}

/// Internal storage representation for the bitmap.
/// This is used during read-modify-write operations to maintain the storage
/// invariants.
///
/// This enum provides a safe abstraction over the two storage modes,
/// allowing controlled transitions between inline and external storage
/// while maintaining all invariants.
///
/// # Why BitArray?
///
/// Direct manipulation of SmolBitmap's packed representation is unsafe
/// because storage mode transitions require careful handling of:
/// - Memory allocation/deallocation
/// - Pointer encoding/decoding
/// - Capacity preservation
/// - MSB constraints
///
/// BitArray ensures these invariants are maintained during all operations.
pub(crate) enum BitArray {
    /// Inline storage candidate (may be promoted to external if needed)
    InlineCandidate(ArrayBitmap),
    /// External heap-allocated storage
    External(Box<[u64]>),
}

impl Default for BitArray {
    fn default() -> Self {
        Self::InlineCandidate([0; WORDS_INLINE])
    }
}

impl From<Vec<u64>> for BitArray {
    fn from(vec: Vec<u64>) -> Self {
        if let Some(array) = try_inline(&vec) {
            return Self::InlineCandidate(array);
        }
        Self::External(vec.into_boxed_slice())
    }
}

impl From<Box<[u64]>> for BitArray {
    fn from(words: Box<[u64]>) -> Self {
        Self::External(words)
    }
}

impl From<&[u64]> for BitArray {
    fn from(slice: &[u64]) -> Self {
        if let Some(array) = try_inline(slice) {
            return Self::InlineCandidate(array);
        }
        Self::External(slice.into())
    }
}

impl BitArray {
    /// Creates a BitArray from raw pointer and length.
    /// # Safety
    /// The caller must ensure that:
    /// - `data` is a valid pointer from `Vec::into_raw_parts`
    /// - `len` is the capacity (not length!) of the original allocation
    /// - `data` points to a properly aligned allocation of `len *
    ///   size_of::<u64>()` bytes
    /// - The pointer has not been freed and is not aliased
    unsafe fn from_raw(data: *mut u64, len: usize) -> Self {
        // SAFETY: Caller guarantees that:
        // - data is a valid pointer from Vec::into_raw_parts
        // - len is the capacity (not length!) of the original allocation
        // - data points to a properly aligned allocation of len * size_of::<u64>()
        //   bytes
        // Using len for both length and capacity preserves the full allocation
        Self::External(unsafe { Box::from_raw(slice::from_raw_parts_mut(data, len)) })
    }

    /// Reconstructs a BitArray from a finalized array representation.
    /// If the MSB of the last word is clear, it's inline storage.
    /// Otherwise, it's external storage encoded as [ptr, -capacity].
    ///
    /// # Note on Capacity vs Length
    /// The second word in external storage encodes the capacity (not length!)
    /// as a negative value. This preserves the original allocation size,
    /// allowing efficient resize operations without reallocation.
    pub(crate) unsafe fn unpack(array: ArrayBitmap) -> Self {
        if !msb(array[WORDS_INLINE - 1]) {
            Self::InlineCandidate(array)
        } else {
            let ptr = array[0] as usize as *mut u64;
            let len = (array[1] as i64).unsigned_abs() as usize;
            unsafe { Self::from_raw(ptr, len) }
        }
    }

    pub(crate) fn with_capacity(bits: usize) -> Self {
        if bits <= BITS_INLINE {
            Self::InlineCandidate([0; WORDS_INLINE])
        } else {
            Self::External(vec![0; bits.div_ceil(64)].into_boxed_slice())
        }
    }

    /// Converts the BitArray into its finalized array representation.
    /// For inline storage, returns the array as-is.
    /// For external storage, returns [ptr, -capacity] with MSB set in the
    /// second word.
    ///
    /// # Capacity Preservation
    /// External storage encodes the allocation capacity (not the logical
    /// length!) to preserve reserved space across pack/unpack cycles. This
    /// prevents unnecessary reallocations when the bitmap grows and shrinks.
    pub(crate) fn pack(self) -> ArrayBitmap {
        let mut vec = match self {
            Self::InlineCandidate(array) => {
                // If MSB is set in inline candidate, we need to spill to external
                if (array[WORDS_INLINE - 1] as i64) >= 0 {
                    return array;
                }
                inline_promote(&array)
            }
            Self::External(arr) if !arr.is_empty() => arr.into_vec(),
            _ => return Default::default(),
        };

        // Manual implementation of vec.into_raw_parts()
        let ptr = vec.as_mut_ptr();
        let len = vec.len();
        let cap = vec.capacity();
        mem::forget(vec);

        debug_assert!(cap >= WORDS_INLINE);
        // Zero out unused capacity to maintain invariants
        if cap > len {
            unsafe {
                slice::from_raw_parts_mut(ptr.add(len), cap - len).fill(0);
            }
        }
        // Encode as [ptr, -capacity] where -capacity has MSB set
        // Using capacity (not length) preserves the allocation size
        [ptr as usize as u64, (-(cap as i64)) as u64]
    }

    /// Resize the storage to the new length, filling new elements with the
    /// specified value. The new length must be strictly greater than the
    /// current length.
    pub(crate) fn extend_to(&mut self, new_len: usize, fill_value: u64) {
        let mut vec = match mem::take(self) {
            Self::External(arr) => arr.into_vec(),
            Self::InlineCandidate(array) => {
                let new_len = new_len.max(WORDS_MINEXT);
                let mut vec = Vec::with_capacity(new_len);
                vec.extend_from_slice(&array);
                vec
            }
        };
        vec.resize(new_len, fill_value);
        *self = Self::External(vec.into_boxed_slice());
    }

    /// Truncate the storage to the specified length.
    pub(crate) fn truncate(&mut self, len: usize) {
        for v in self.iter_mut().skip(len) {
            *v = 0;
        }
    }

    /// Extend the storage with elements from a slice.
    pub(crate) fn extend_from_slice(&mut self, slice: &[u64]) {
        let vec = match mem::take(self) {
            Self::External(arr) => {
                let mut vec = arr.into_vec();
                vec.extend_from_slice(slice);
                vec
            }
            Self::InlineCandidate(arr) => {
                let mut vec = Vec::with_capacity(arr.len() + slice.len());
                vec.extend_from_slice(&arr);
                vec.extend_from_slice(slice);
                vec
            }
        };
        *self = Self::External(vec.into_boxed_slice());
    }

    /// Reduce capacity to match the current length.
    pub(crate) fn shrink_to_fit(&mut self) {
        let Self::External(array) = self else {
            return;
        };
        let slice = rtrim0(array.as_ref());
        if let Some(array) = try_inline(slice) {
            *self = Self::InlineCandidate(array);
            return;
        }

        let slice_n = slice.len();
        if slice_n < array.len() {
            let mut vec = mem::take(array).into_vec();
            vec.truncate(slice_n);
            vec.shrink_to_fit();
            *array = vec.into_boxed_slice()
        }
    }

    pub(crate) fn into_vec(self) -> Vec<u64> {
        match self {
            Self::External(array) => array.into_vec(),
            Self::InlineCandidate(array) => inline_promote(&array),
        }
    }
}

impl Deref for BitArray {
    type Target = [u64];

    fn deref(&self) -> &Self::Target {
        match self {
            Self::External(vec) => vec,
            Self::InlineCandidate(array) => array,
        }
    }
}

impl DerefMut for BitArray {
    fn deref_mut(&mut self) -> &mut Self::Target {
        match self {
            Self::External(vec) => vec,
            Self::InlineCandidate(array) => array,
        }
    }
}

impl AsRef<[u64]> for BitArray {
    fn as_ref(&self) -> &[u64] {
        self
    }
}

impl AsMut<[u64]> for BitArray {
    fn as_mut(&mut self) -> &mut [u64] {
        match self {
            Self::External(vec) => vec,
            Self::InlineCandidate(array) => array,
        }
    }
}

impl Borrow<[u64]> for BitArray {
    fn borrow(&self) -> &[u64] {
        self
    }
}

impl Index<usize> for BitArray {
    type Output = u64;

    fn index(&self, index: usize) -> &Self::Output {
        match self {
            Self::External(vec) => &vec[index],
            Self::InlineCandidate(array) => &array[index],
        }
    }
}

impl IndexMut<usize> for BitArray {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        match self {
            Self::External(vec) => &mut vec[index],
            Self::InlineCandidate(array) => &mut array[index],
        }
    }
}

/// A builder for efficiently constructing bitmaps from raw word data.
///
/// `SmolBitmapBuilder` provides an efficient way to construct bitmaps when
/// you're working with raw 64-bit words. It automatically handles the
/// transition between inline and heap storage based on the data size.
///
/// # Examples
///
/// ```
/// use smol_bitmap::SmolBitmapBuilder;
///
/// let mut builder = SmolBitmapBuilder::with_capacity(2);
/// builder.push(0b1010101010101010_u64); // First word
/// builder.push(0b1111000011110000_u64); // Second word
/// let bitmap = builder.finalize();
///
/// assert!(bitmap.get(1));
/// assert!(!bitmap.get(0));
/// ```
pub enum SmolBitmapBuilder {
    #[doc(hidden)]
    Inline([u64; WORDS_INLINE], usize),
    #[doc(hidden)]
    External(Vec<u64>),
}

impl SmolBitmapBuilder {
    /// Creates a new builder with the specified word capacity.
    ///
    /// If the capacity is small enough for inline storage (≤2 words),
    /// the builder will use inline storage. Otherwise, it allocates
    /// heap storage.
    ///
    /// # Arguments
    ///
    /// * `words` - The number of 64-bit words to reserve capacity for
    ///
    /// # Examples
    ///
    /// ```
    /// use smol_bitmap::SmolBitmapBuilder;
    ///
    /// // Small capacity uses inline storage
    /// let builder = SmolBitmapBuilder::with_capacity(2);
    ///
    /// // Large capacity uses heap storage
    /// let builder = SmolBitmapBuilder::with_capacity(10);
    /// ```
    pub fn with_capacity(words: usize) -> Self {
        if words <= WORDS_INLINE {
            Self::Inline([0; WORDS_INLINE], 0)
        } else {
            Self::External(Vec::with_capacity(words))
        }
    }

    /// Returns a mutable slice of the words currently in the builder.
    ///
    /// # Examples
    ///
    /// ```
    /// use smol_bitmap::SmolBitmapBuilder;
    ///
    /// let mut builder = SmolBitmapBuilder::with_capacity(2);
    /// builder.push(0xFFFF);
    /// let slice = builder.as_mut_slice();
    /// slice[0] |= 0xFF00;
    /// ```
    pub fn as_mut_slice(&mut self) -> &mut [u64] {
        match self {
            Self::Inline(a, n) => &mut a[..*n],
            Self::External(v) => v.as_mut_slice(),
        }
    }

    /// Appends a 64-bit word to the builder.
    ///
    /// If the builder was using inline storage and adding this word
    /// would exceed inline capacity, it automatically transitions to
    /// heap storage.
    ///
    /// # Arguments
    ///
    /// * `word` - The 64-bit word to append
    ///
    /// # Examples
    ///
    /// ```
    /// use smol_bitmap::SmolBitmapBuilder;
    ///
    /// let mut builder = SmolBitmapBuilder::with_capacity(2);
    /// builder.push(0b1111_0000);
    /// builder.push(0b0000_1111);
    /// ```
    pub fn push(&mut self, word: u64) {
        match self {
            Self::Inline(a, n) => {
                if *n < WORDS_INLINE {
                    a[*n] = word;
                    *n += 1;
                } else {
                    let mut v = Vec::with_capacity(WORDS_INLINE << 1);
                    v.extend_from_slice(&a[..*n]);
                    v.push(word);
                    *self = Self::External(v);
                }
            }
            Self::External(v) => {
                v.push(word);
            }
        }
    }

    /// Extend the builder with a slice of words.
    ///
    /// If the builder was using inline storage and adding this slice
    /// would exceed inline capacity, it automatically transitions to
    /// heap storage.
    ///
    /// # Arguments
    ///
    /// * `slice` - The slice of 64-bit words to extend the builder with
    ///
    /// # Examples
    ///
    /// ```
    /// use smol_bitmap::SmolBitmapBuilder;
    ///
    /// let mut builder = SmolBitmapBuilder::with_capacity(2);
    /// builder.extend_from_slice(&[!0, !0]);
    /// ```
    pub fn extend_from_slice(&mut self, slice: &[u64]) {
        match self {
            Self::Inline(a, n) => {
                let new_len = *n + slice.len();
                if new_len <= WORDS_INLINE {
                    a[*n..new_len].copy_from_slice(slice);
                    *n = new_len;
                } else {
                    let mut v = Vec::with_capacity(new_len);
                    v.extend_from_slice(&a[..*n]);
                    v.extend_from_slice(slice);
                    *self = Self::External(v);
                }
            }
            Self::External(v) => {
                v.extend_from_slice(slice);
            }
        }
    }

    /// Consumes the builder and returns the constructed bitmap.
    ///
    /// This method efficiently converts the accumulated words into
    /// a `SmolBitmap`, using inline storage when possible.
    ///
    /// # Examples
    ///
    /// ```
    /// use smol_bitmap::SmolBitmapBuilder;
    ///
    /// let mut builder = SmolBitmapBuilder::with_capacity(1);
    /// builder.push(0b1010);
    /// let bitmap = builder.finalize();
    ///
    /// assert!(bitmap.get(1));
    /// assert!(!bitmap.get(0));
    /// assert!(bitmap.get(3));
    /// assert!(!bitmap.get(2));
    /// ```
    pub fn finalize(self) -> crate::SmolBitmap {
        match self {
            Self::Inline(a, n) => crate::SmolBitmap::from(&a[..n]),
            Self::External(v) => crate::SmolBitmap::from(v),
        }
    }
}
