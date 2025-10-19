//! Internal storage representation and management for the bitmap.

use alloc::{boxed::Box, vec, vec::Vec};
use core::{
    borrow::Borrow,
    iter,
    mem::{self, MaybeUninit},
    ops::{Deref, DerefMut, Index, IndexMut},
    ptr, slice,
};

use crate::{SmolBitmap, macros::msb};

/// Number of 64-bit words that can be stored inline
pub(crate) const WORDS_INLINE: usize = 2;
pub(crate) const WORDS_MINEXT: usize = 4;
pub(crate) const BITS_INLINE: usize = 64 * WORDS_INLINE - 1;

pub(crate) type ArrayBitmap = [u64; WORDS_INLINE];

/// Attempts to pack words into inline storage.
/// Returns Some(array) if the words can fit inline, None otherwise.
/// Words can fit inline if:
/// 1. There are at most `INLINE_QWORDS` non-zero words
/// 2. The last word has its MSB clear (to distinguish from external storage)
/// 3. The actual bits used don't exceed `INLINE_CAPACITY`
#[inline(always)]
pub(crate) fn try_inline(words: impl AsRef<[u64]>) -> Option<ArrayBitmap> {
    let words = words.as_ref();
    if words.len() <= WORDS_INLINE {
        if let Ok(array) = <ArrayBitmap>::try_from(words)
            && msb!(array[WORDS_INLINE - 1])
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
/// Creates an intermediate array to ensure `MIN_EXTERNAL` capacity, which
/// avoids the allocation churn that would happen with capacity ==
/// `INLINE_QWORDS`.
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
/// # Why `BitArray`?
///
/// Direct manipulation of `SmolBitmap`'s packed representation is unsafe
/// because storage mode transitions require careful handling of:
/// - Memory allocation/deallocation
/// - Pointer encoding/decoding
/// - Capacity preservation
/// - MSB constraints
///
/// `BitArray` ensures these invariants are maintained during all operations.
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

impl<const N: usize> From<&[u64; N]> for BitArray {
    fn from(slice: &[u64; N]) -> Self {
        if let Some(array) = try_inline(slice) {
            return Self::InlineCandidate(array);
        }
        Self::External(slice.to_vec().into_boxed_slice())
    }
}

impl BitArray {
    /// Creates a `BitArray` from raw pointer and length.
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

    /// Reconstructs a `BitArray` from a finalized array representation.
    /// If the MSB of the last word is clear, it's inline storage.
    /// Otherwise, it's external storage encoded as [ptr, -capacity].
    ///
    /// # Note on Capacity vs Length
    /// The second word in external storage encodes the capacity (not length!)
    /// as a negative value. This preserves the original allocation size,
    /// allowing efficient resize operations without reallocation.
    pub(crate) unsafe fn unpack(array: ArrayBitmap) -> Self {
        if msb!(array[WORDS_INLINE - 1]) {
            let ptr = array[0] as usize as *mut u64;
            let len = (array[1] as i64).unsigned_abs() as usize;
            unsafe { Self::from_raw(ptr, len) }
        } else {
            Self::InlineCandidate(array)
        }
    }

    pub(crate) fn with_capacity(bits: usize) -> Self {
        if bits <= BITS_INLINE {
            Self::InlineCandidate([0; WORDS_INLINE])
        } else {
            Self::External(vec![0; bits.div_ceil(64)].into_boxed_slice())
        }
    }

    /// Converts the `BitArray` into its finalized array representation.
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
                if !msb!(array[WORDS_INLINE - 1]) {
                    return array;
                }
                inline_promote(&array)
            }
            Self::External(arr) if !arr.is_empty() => arr.into_vec(),
            Self::External(_) => return Default::default(),
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
        if len < self.len() {
            unsafe { self.as_mut().get_unchecked_mut(len..).fill(0) };
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
            *array = vec.into_boxed_slice();
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

#[doc(hidden)]
#[derive(Debug, Clone, Copy)]
pub struct StackVec {
    data: MaybeUninit<ArrayBitmap>,
    len: u8,
}

impl Default for StackVec {
    fn default() -> Self {
        Self::new()
    }
}

const MIN_ALLOC: usize = 16;

impl From<ArrayBitmap> for StackVec {
    fn from(array: ArrayBitmap) -> Self {
        Self {
            data: MaybeUninit::new(array),
            len: array.len() as u8,
        }
    }
}

impl StackVec {
    #[inline(always)]
    #[must_use]
    pub const fn new() -> Self {
        Self {
            data: MaybeUninit::uninit(),
            len: 0,
        }
    }

    #[inline(always)]
    pub fn from_slice(slice: &[u64]) -> Result<Self, &[u64]> {
        let mut vec = Self::new();
        vec.extend_from_slice(slice)?;
        Ok(vec)
    }

    #[inline(always)]
    #[must_use]
    pub const fn len(&self) -> usize {
        self.len as usize
    }

    #[inline(always)]
    #[allow(dead_code)]
    #[must_use]
    pub const fn is_empty(&self) -> bool {
        self.len == 0
    }

    #[inline]
    pub const fn extend_from_slice<'s>(&mut self, slice: &'s [u64]) -> Result<(), &'s [u64]> {
        let len = self.len();
        let new_len = len + slice.len();
        if new_len > WORDS_INLINE {
            return Err(slice);
        }
        unsafe {
            ptr::copy_nonoverlapping(
                slice.as_ptr(),
                self.data.as_mut_ptr().add(len).cast::<u64>(),
                slice.len(),
            );
        }
        self.len = new_len as u8;
        Ok(())
    }

    #[inline]
    pub fn push(&mut self, word: u64) -> Result<(), u64> {
        let len = self.len();
        if len == WORDS_INLINE {
            return Err(word);
        }
        unsafe {
            *self.data.assume_init_mut().get_unchecked_mut(len) = word;
        }
        self.len = (len + 1) as u8;
        Ok(())
    }

    #[inline(always)]
    #[must_use]
    pub fn as_slice(&self) -> &[u64] {
        let n = self.len();
        unsafe { self.data.assume_init_ref().get_unchecked(..n) }
    }

    #[inline(always)]
    pub fn as_mut_slice(&mut self) -> &mut [u64] {
        let n = self.len();
        unsafe { &mut *self.data.assume_init_mut().get_unchecked_mut(..n) }
    }

    #[inline(always)]
    pub fn resize(&mut self, len: usize, word: u64) -> Result<(), usize> {
        let prev = self.len();
        if prev < len {
            if len > WORDS_INLINE {
                return Err(len - prev);
            }
            unsafe {
                self.data
                    .assume_init_mut()
                    .get_unchecked_mut(prev..len)
                    .fill(word);
            }
        }
        self.len = len as u8;
        Ok(())
    }

    #[inline(always)]
    pub fn extend_into_vec<I>(&self, rhs: I) -> Vec<u64>
    where
        I: IntoIterator<Item = u64>,
    {
        let lhs = self.as_slice();
        let rhs = rhs.into_iter();

        let (rlen, _) = rhs.size_hint();
        let mut v = Vec::with_capacity((lhs.len() + rlen).max(MIN_ALLOC));
        v.extend_from_slice(lhs);
        v.extend(rhs);
        v
    }

    pub fn try_extend<I>(&mut self, other: I) -> Result<(), Vec<u64>>
    where
        I: IntoIterator<Item = u64>,
    {
        let mut other = other.into_iter().peekable();
        while let Some(word) = other.peek() {
            if self.push(*word).is_ok() {
                other.next();
                continue;
            }
            return Err(self.extend_into_vec(other));
        }
        Ok(())
    }

    #[inline(always)]
    #[must_use]
    pub const fn capacity(&self) -> usize {
        WORDS_INLINE
    }

    #[inline(always)]
    #[must_use]
    pub const fn as_ptr(&self) -> *const u64 {
        self.data.as_ptr().cast::<u64>()
    }

    #[inline(always)]
    pub const fn as_mut_ptr(&mut self) -> *mut u64 {
        self.data.as_mut_ptr().cast::<u64>()
    }

    #[inline(always)]
    pub fn set_len(&mut self, new_len: usize) {
        debug_assert!(new_len <= WORDS_INLINE);
        self.len = new_len as u8;
    }

    #[inline(always)]
    pub fn reserve(&mut self, additional: usize) -> Result<(), Vec<u64>> {
        let new_len = self.len() + additional;
        if new_len > WORDS_INLINE {
            let mut vec = Vec::with_capacity(new_len.max(MIN_ALLOC));
            vec.extend_from_slice(self.as_slice());
            return Err(vec);
        }
        Ok(())
    }

    #[inline(always)]
    pub fn spare_capacity_mut(&mut self) -> &mut [MaybeUninit<u64>] {
        let n = self.len();
        unsafe {
            &mut *ptr::slice_from_raw_parts_mut(
                self.data.as_mut_ptr().add(n).cast::<MaybeUninit<u64>>(),
                WORDS_INLINE - n,
            )
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
    Inline(StackVec),
    #[doc(hidden)]
    External(Vec<u64>),
}

impl From<&[u64]> for SmolBitmapBuilder {
    fn from(slice: &[u64]) -> Self {
        Self::from_slice(slice)
    }
}

impl From<Vec<u64>> for SmolBitmapBuilder {
    fn from(vec: Vec<u64>) -> Self {
        Self::External(vec)
    }
}

impl From<SmolBitmapBuilder> for SmolBitmap {
    fn from(builder: SmolBitmapBuilder) -> Self {
        builder.finalize()
    }
}

impl From<SmolBitmap> for SmolBitmapBuilder {
    fn from(bitmap: SmolBitmap) -> Self {
        match bitmap.into_inner() {
            BitArray::InlineCandidate(array) => Self::Inline(StackVec::from(array)),
            BitArray::External(alloc) => Self::External(alloc.into_vec()),
        }
    }
}

impl FromIterator<u64> for SmolBitmapBuilder {
    fn from_iter<T: IntoIterator<Item = u64>>(iter: T) -> Self {
        let mut builder = Self::new();
        builder.extend(iter);
        builder
    }
}

impl Default for SmolBitmapBuilder {
    fn default() -> Self {
        Self::new()
    }
}

impl SmolBitmapBuilder {
    /// Creates a new, empty `SmolBitmapBuilder`.
    ///
    /// This method initializes a new `SmolBitmapBuilder` with inline storage.
    /// It is suitable for small bitmaps that fit within the inline storage
    /// capacity.
    ///
    /// # Examples
    ///
    /// ```
    /// use smol_bitmap::SmolBitmapBuilder;
    ///
    /// let builder = SmolBitmapBuilder::new();
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn new() -> Self {
        Self::Inline(StackVec::new())
    }

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
    #[must_use]
    pub fn with_capacity(words: usize) -> Self {
        if words <= WORDS_INLINE {
            Self::Inline(StackVec::new())
        } else {
            Self::External(Vec::with_capacity(words))
        }
    }

    /// Creates a `SmolBitmapBuilder` from a slice of 64-bit words.
    ///
    /// This method initializes the builder with the words from the provided
    /// slice. If the slice length is small enough for inline storage (≤2
    /// words), the builder will use inline storage. Otherwise, it allocates
    /// heap storage.
    ///
    /// # Arguments
    ///
    /// * `slice` - A slice of 64-bit words to initialize the builder with
    ///
    /// # Examples
    ///
    /// ```
    /// use smol_bitmap::SmolBitmapBuilder;
    ///
    /// let words = [0b10101010, 0b11110000];
    /// let builder = SmolBitmapBuilder::from_slice(&words);
    /// ```
    #[must_use]
    pub fn from_slice(slice: &[u64]) -> Self {
        StackVec::from_slice(slice).map_or_else(|s| Self::External(s.to_vec()), Self::Inline)
    }

    /// Returns a slice of the words currently in the builder.
    ///
    /// # Examples
    ///
    /// ```
    /// use smol_bitmap::SmolBitmapBuilder;
    ///
    /// let mut builder = SmolBitmapBuilder::with_capacity(2);
    /// builder.push(0xFFFF);
    /// let slice = builder.as_slice();
    /// assert_eq!(slice, &[0xFFFF]);
    /// ```
    #[must_use]
    pub fn as_slice(&self) -> &[u64] {
        match self {
            Self::Inline(a) => a.as_slice(),
            Self::External(v) => v.as_slice(),
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
            Self::Inline(a) => a.as_mut_slice(),
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
            Self::Inline(a) => {
                if let Err(word) = a.push(word) {
                    *self = Self::External(a.extend_into_vec([word]));
                }
            }
            Self::External(v) => {
                v.push(word);
            }
        }
    }

    /// Resizes the builder to the specified length, filling new slots with the
    /// given word.
    ///
    /// If the builder was using inline storage and resizing would exceed inline
    /// capacity, it automatically transitions to heap storage.
    ///
    /// # Arguments
    ///
    /// * `len` - The new length of the builder.
    /// * `word` - The 64-bit word to fill new slots with if the builder is
    ///   expanded.
    ///
    /// # Examples
    ///
    /// ```
    /// use smol_bitmap::SmolBitmapBuilder;
    ///
    /// let mut builder = SmolBitmapBuilder::with_capacity(2);
    /// builder.push(0b1111_0000);
    /// builder.resize(4, 0b0000_1111);
    /// ```
    pub fn resize(&mut self, len: usize, word: u64) {
        match self {
            Self::Inline(a) => {
                if let Err(n) = a.resize(len, word) {
                    *self = Self::External(a.extend_into_vec(iter::repeat_n(word, n)));
                }
            }
            Self::External(v) => v.resize(len, word),
        }
    }

    /// Returns the remaining spare capacity of the builder as a slice of
    /// `MaybeUninit<u64>`.
    ///
    /// This method allows you to safely initialize additional elements in the
    /// builder without reallocating. After writing to the returned slice, you
    /// must call a method like `set_len` to update the length of the builder.
    ///
    /// # Examples
    ///
    /// ```
    /// use core::mem::MaybeUninit;
    /// use smol_bitmap::SmolBitmapBuilder;
    ///
    /// let mut builder = SmolBitmapBuilder::with_capacity(10);
    /// let spare_capacity = builder.spare_capacity_mut();
    /// assert!(spare_capacity.len() >= 10);
    /// ```
    pub fn spare_capacity_mut(&mut self) -> &mut [MaybeUninit<u64>] {
        match self {
            Self::Inline(a) => a.spare_capacity_mut(),
            Self::External(v) => v.spare_capacity_mut(),
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
            Self::Inline(a) => {
                if let Err(s) = a.extend_from_slice(slice) {
                    *self = Self::External(a.extend_into_vec(s.iter().copied()));
                }
            }
            Self::External(v) => {
                v.extend_from_slice(slice);
            }
        }
    }

    /// Returns the current capacity of the builder.
    ///
    /// This represents the number of 64-bit words the builder can hold
    /// without reallocating.
    ///
    /// # Examples
    ///
    /// ```
    /// use smol_bitmap::SmolBitmapBuilder;
    ///
    /// let builder = SmolBitmapBuilder::with_capacity(10);
    /// assert_eq!(builder.capacity(), 10);
    /// ```
    #[must_use]
    pub const fn capacity(&self) -> usize {
        match self {
            Self::Inline(a) => a.capacity(),
            Self::External(v) => v.capacity(),
        }
    }

    /// Returns a raw pointer to the builder's buffer.
    ///
    /// This pointer is valid for reads, but not writes, and is only valid
    /// as long as the builder is not modified.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the builder is not modified while the
    /// pointer is in use.
    ///
    /// # Examples
    ///
    /// ```
    /// use smol_bitmap::SmolBitmapBuilder;
    ///
    /// let builder = SmolBitmapBuilder::with_capacity(1);
    /// let ptr = builder.as_ptr();
    /// ```
    #[must_use]
    pub const fn as_ptr(&self) -> *const u64 {
        match self {
            Self::Inline(a) => a.as_ptr(),
            Self::External(v) => v.as_ptr(),
        }
    }

    /// Returns a mutable raw pointer to the builder's buffer.
    ///
    /// This pointer is valid for both reads and writes, and is only valid
    /// as long as the builder is not reallocated.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the builder is not reallocated while the
    /// pointer is in use.
    ///
    /// # Examples
    ///
    /// ```
    /// use smol_bitmap::SmolBitmapBuilder;
    ///
    /// let mut builder = SmolBitmapBuilder::with_capacity(1);
    /// let ptr = builder.as_mut_ptr();
    /// ```
    pub const fn as_mut_ptr(&mut self) -> *mut u64 {
        match self {
            Self::Inline(a) => a.as_mut_ptr(),
            Self::External(v) => v.as_mut_ptr(),
        }
    }

    /// Sets the length of the builder.
    ///
    /// This method allows for manual adjustment of the builder's length.
    /// It is the caller's responsibility to ensure that the new length
    /// does not exceed the capacity.
    ///
    /// # Safety
    ///
    /// This function is unsafe because it does not check if the new length
    /// is valid. The caller must ensure that the new length is within the
    /// capacity and that all elements are properly initialized.
    ///
    /// # Examples
    ///
    /// ```
    /// use smol_bitmap::SmolBitmapBuilder;
    ///
    /// let mut builder = SmolBitmapBuilder::with_capacity(2);
    /// unsafe { builder.set_len(1) };
    /// ```
    pub unsafe fn set_len(&mut self, new_len: usize) {
        unsafe {
            match self {
                Self::Inline(a) => a.set_len(new_len),
                Self::External(v) => v.set_len(new_len),
            }
        }
    }

    /// Reserves capacity for at least `additional` more words to be inserted
    /// in the builder. The collection may reserve more space to avoid frequent
    /// reallocations.
    ///
    /// If the builder is using inline storage and the additional capacity
    /// would exceed the inline limit, it transitions to heap storage.
    ///
    /// # Arguments
    ///
    /// * `additional` - The number of additional 64-bit words to reserve space
    ///   for.
    pub fn reserve(&mut self, additional: usize) {
        match self {
            Self::Inline(a) => {
                if let Err(vec) = a.reserve(additional) {
                    *self = Self::External(vec);
                }
            }
            Self::External(v) => {
                v.reserve(additional);
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
    #[must_use]
    pub fn finalize(self) -> SmolBitmap {
        match self {
            Self::Inline(a) => SmolBitmap::from(a.as_slice()),
            Self::External(v) => SmolBitmap::from(v),
        }
    }
}

impl Extend<u64> for SmolBitmapBuilder {
    fn extend<I>(&mut self, iter: I)
    where
        I: IntoIterator<Item = u64>,
    {
        let iter = iter.into_iter();
        let (iter_len, _) = iter.size_hint();
        self.reserve(iter_len);
        match self {
            Self::Inline(a) => {
                if let Err(vec) = a.try_extend(iter) {
                    *self = Self::External(vec);
                }
            }
            Self::External(v) => v.extend(iter),
        }
    }
}

impl Deref for SmolBitmapBuilder {
    type Target = [u64];

    fn deref(&self) -> &Self::Target {
        self.as_slice()
    }
}

impl DerefMut for SmolBitmapBuilder {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.as_mut_slice()
    }
}
