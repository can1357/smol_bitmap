//! `SmolBitmap` struct and core implementation.

use core::{
    cmp::{self, Ordering},
    hint, mem,
    ops::Index,
    slice,
};

use crate::{
    iter::{BitIter, Iter, SelectIter},
    macros::{bitpos, msb},
    storage::{ArrayBitmap, BITS_INLINE, BitArray, SmolBitmapBuilder, WORDS_INLINE, rtrim0},
};

/// A compact bitmap that stores bits either inline or on the heap.
///
/// # Overview
///
/// `SmolBitmap` provides efficient storage for bit flags with automatic
/// promotion from inline storage to heap allocation when needed. It's designed
/// for scenarios where you frequently need small bitmaps but occasionally
/// require larger ones.
///
/// # Storage Strategy
///
/// - **Inline**: Up to `SmolBitmap::inline_capacity()` bits stored directly in
///   the struct
/// - **Heap**: Automatically switches to heap allocation for larger bitmaps
/// - The highest bit of the last word indicates storage mode (0 = inline, 1 =
///   heap)
///
/// # Capacity Model
///
/// Unlike typical collections, `SmolBitmap` unifies length and capacity. All
/// bits up to the capacity are accessible, with unset bits returning `false`.
///
/// # Internal Representation
///
/// The `words` field has dual purpose:
/// - Inline mode: Contains the actual bit data
/// - External mode: Contains [pointer, -length] where length is negative to set
///   MSB
///
/// # Examples
///
/// ```
/// use smol_bitmap::SmolBitmap;
/// let mut bitmap = SmolBitmap::new();
///
/// // Set some bits
/// bitmap.insert(10);
/// bitmap.insert(100);
///
/// // Check bits
/// assert!(bitmap.get(10));
/// assert!(bitmap.get(100));
/// assert!(!bitmap.get(50)); // Unset bits are false
///
/// // Force heap allocation
/// bitmap.insert(200);
/// assert!(bitmap.is_spilled()); // Now using heap storage
/// ```
#[repr(transparent)]
pub struct SmolBitmap {
    pub(crate) array: ArrayBitmap,
}

impl SmolBitmap {
    /// Creates a new empty bitmap with inline storage.
    ///
    /// The bitmap starts with inline storage capacity (127 bits) and will
    /// automatically promote to heap storage if needed.
    ///
    /// # Examples
    ///
    /// ```
    /// # use smol_bitmap::SmolBitmap;
    /// let bitmap = SmolBitmap::new();
    /// assert_eq!(bitmap.capacity(), SmolBitmap::inline_capacity());
    /// assert!(!bitmap.is_spilled());
    /// ```
    #[must_use]
    pub const fn new() -> Self {
        Self {
            array: [0; WORDS_INLINE],
        }
    }

    /// Returns the maximum number of bits that can be stored in inline storage.
    ///
    /// This is 127 bits (2 × 64 - 1), as the highest bit is reserved for
    /// storage mode indication.
    ///
    /// # Examples
    ///
    /// ```
    /// # use smol_bitmap::SmolBitmap;
    /// assert_eq!(SmolBitmap::inline_capacity(), 127);
    /// ```
    #[must_use]
    pub const fn inline_capacity() -> usize {
        BITS_INLINE
    }

    /// Retains only the elements specified by the predicate.
    ///
    /// Removes all bits `bit` such that `f(bit)` returns `false`. This
    /// operation is performed in-place and efficiently processes bits word
    /// by word.
    ///
    /// # Arguments
    ///
    /// * `f` - A predicate function that takes a bit index and returns `true`
    ///   if the bit should be retained
    ///
    /// # Examples
    ///
    /// ```
    /// # use smol_bitmap::SmolBitmap;
    /// let mut bitmap = SmolBitmap::new();
    /// bitmap.insert(1);
    /// bitmap.insert(2);
    /// bitmap.insert(5);
    /// bitmap.insert(8);
    ///
    /// // Retain only even indices
    /// bitmap.retain(|bit| bit % 2 == 0);
    ///
    /// assert!(!bitmap.get(1));
    /// assert!(bitmap.get(2));
    /// assert!(!bitmap.get(5));
    /// assert!(bitmap.get(8));
    /// ```
    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(usize) -> bool,
    {
        // SAFETY: We're only reading and modifying individual bits, not the MSB
        let rb = unsafe { self.as_mut_slice() };
        for (wi, word) in rb.iter_mut().enumerate() {
            let mut rem = *word;
            while rem != 0 {
                let rel = rem.trailing_zeros() as usize;
                let bi = wi * 64 + rel;
                let nmask = !(1 << rel);
                if !f(bi) {
                    *word &= nmask;
                }
                rem &= nmask;
            }
        }
    }

    /// Creates a new bitmap with at least the specified bit capacity.
    ///
    /// If the capacity is within the inline limit
    /// ([`inline_capacity`](Self::inline_capacity)), the bitmap will use
    /// inline storage. Otherwise, it will allocate heap storage.
    ///
    /// # Examples
    ///
    /// ```
    /// # use smol_bitmap::SmolBitmap;
    /// // Small capacity uses inline storage
    /// let bitmap = SmolBitmap::with_capacity(100);
    /// assert!(!bitmap.is_spilled());
    ///
    /// // Large capacity uses heap storage
    /// let bitmap = SmolBitmap::with_capacity(1000);
    /// assert!(bitmap.is_spilled());
    /// ```
    #[must_use]
    pub fn with_capacity(bits: usize) -> Self {
        Self {
            array: BitArray::with_capacity(bits).pack(),
        }
    }

    /// Returns `true` if the bitmap is using heap storage.
    ///
    /// # Examples
    ///
    /// ```
    /// # use smol_bitmap::SmolBitmap;
    /// let mut bitmap = SmolBitmap::new();
    /// assert!(!bitmap.is_spilled());
    ///
    /// bitmap.insert(200); // Beyond inline capacity
    /// assert!(bitmap.is_spilled());
    /// ```
    #[must_use]
    #[inline(always)]
    pub const fn is_spilled(&self) -> bool {
        (self.array[WORDS_INLINE - 1] as i64) < 0
    }

    /// Get the pointer to external storage.
    /// # Safety
    /// This function is only valid if `is_spilled` returns true.
    /// The pointer is encoded in the first word when using external storage.
    const fn external_ptr(&self) -> *mut u64 {
        debug_assert!(self.is_spilled());
        self.array[0] as *mut u64
    }

    /// Get the word length of external storage.
    /// # Safety
    /// This function is only valid if `is_spilled` returns true.
    /// The length is encoded as negative in the second word to ensure MSB is
    /// set.
    #[inline(always)]
    const fn external_word_count(&self) -> usize {
        debug_assert!(self.is_spilled());
        // Cast to i64 to handle the negative encoding
        let encoded = self.array[WORDS_INLINE - 1] as i64;
        // The value should be negative (MSB set)
        debug_assert!(
            encoded < 0,
            "external storage should have negative length encoding"
        );
        // Negate to get the actual length
        let n = encoded.wrapping_neg();
        assert!((n > 0), "external word count should be positive");
        debug_assert!(n > 0, "external word count should be positive");
        n as usize
    }

    /// Get the number of words in storage
    #[inline(always)]
    const fn word_count(&self) -> usize {
        if self.is_spilled() {
            self.external_word_count()
        } else {
            WORDS_INLINE
        }
    }

    /// Get a const pointer to the storage
    #[must_use]
    pub const fn as_ptr(&self) -> *const u64 {
        if self.is_spilled() {
            self.external_ptr()
        } else {
            self.array.as_ptr()
        }
    }

    /// Get a mutable pointer to the storage
    #[inline(always)]
    pub const fn as_mut_ptr(&mut self) -> *mut u64 {
        if self.is_spilled() {
            self.external_ptr()
        } else {
            self.array.as_mut_ptr()
        }
    }

    /// Get the storage as a slice
    #[must_use]
    pub const fn as_slice(&self) -> &[u64] {
        unsafe { slice::from_raw_parts(self.as_ptr(), self.word_count()) }
    }

    /// Get the storage as a mutable slice
    /// # Safety
    /// The caller must ensure that:
    /// - If the storage is inline, the MSB of the last word must not be set
    /// - Modifications must maintain the storage invariants
    /// - The slice must not be extended beyond its capacity
    #[inline(always)]
    pub const unsafe fn as_mut_slice(&mut self) -> &mut [u64] {
        unsafe { slice::from_raw_parts_mut(self.as_mut_ptr(), self.word_count()) }
    }

    /// Returns the total number of bits that can be stored without
    /// reallocation.
    ///
    /// For inline storage, this is always
    /// [`inline_capacity`](Self::inline_capacity). For heap storage, this is
    /// the number of allocated bits.
    ///
    /// # Examples
    ///
    /// ```
    /// # use smol_bitmap::SmolBitmap;
    /// let mut bitmap = SmolBitmap::new();
    /// assert_eq!(bitmap.capacity(), SmolBitmap::inline_capacity());
    /// ```
    #[must_use]
    #[inline(always)]
    pub const fn capacity(&self) -> usize {
        if self.is_spilled() {
            self.external_word_count() * 64
        } else {
            Self::inline_capacity()
        }
    }

    /// Read-Modify-Write helper that maintains storage invariants.
    /// This is the core method for safely modifying the bitmap storage.
    ///
    /// # Safety Contract
    ///
    /// The closure `f` receives a mutable reference to `BitArray` and can
    /// modify it. This pattern ensures:
    /// - Old storage is properly deallocated when transitioning modes
    /// - New storage is properly encoded before being stored
    /// - No memory leaks during storage transitions
    /// - Exception safety (panic = abort in release mode)
    ///
    /// # Example
    ///
    /// ```ignore
    /// bitmap.update(|raw| {
    ///     // Safely modify the bitmap through BitArray interface
    ///     raw.reserve(100);
    /// });
    /// ```
    #[inline(always)]
    pub(crate) fn update<R>(&mut self, f: impl FnOnce(&mut BitArray) -> R) -> R {
        // Read current storage into temporary BitArray
        let mut rb = unsafe { BitArray::unpack(self.array) };
        // Apply the modification
        let r = f(&mut rb);
        // Write back, maintaining invariants
        self.array = rb.pack();
        r
    }

    /// Take the storage out of the bitmap.
    #[inline(always)]
    pub(crate) fn into_inner(self) -> BitArray {
        let rb = unsafe { BitArray::unpack(self.array) };
        mem::forget(self);
        rb
    }

    /// Replace the bitmap with a new empty bitmap, returning the old storage.
    #[inline(always)]
    pub(crate) fn take_inner(&mut self) -> BitArray {
        let prev = mem::replace(&mut self.array, [0; WORDS_INLINE]);
        unsafe { BitArray::unpack(prev) }
    }

    /// Reserves capacity for at least `additional` more bits.
    ///
    /// This method ensures that the bitmap can store at least `additional`
    /// more bits beyond its current capacity. It may reserve more space
    /// to avoid frequent reallocations.
    ///
    /// # Examples
    ///
    /// ```
    /// # use smol_bitmap::SmolBitmap;
    /// let mut bitmap = SmolBitmap::new();
    /// bitmap.reserve(300);
    /// assert!(bitmap.capacity() >= 300);
    /// assert!(bitmap.is_spilled());
    /// ```
    #[cold]
    pub fn reserve(&mut self, additional: usize) {
        if additional == 0 {
            return;
        }

        // If the requested capacity exceeds inline capacity, we must use external
        // storage
        let current_capacity = self.capacity();
        let required_capacity = current_capacity + additional;

        if required_capacity > Self::inline_capacity() {
            // Force transition to external storage
            self.update(
                #[inline(always)]
                |rb| {
                    // Convert to words, rounding up
                    let required_words = required_capacity.div_ceil(64);
                    // Grow to at least the required size, using power of two for efficiency
                    let new_len = required_words.next_power_of_two();
                    rb.extend_to(new_len, 0);
                },
            );
        }
    }

    /// Returns the value of the bit at the given index.
    ///
    /// Returns `false` if the index is out of bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// # use smol_bitmap::SmolBitmap;
    /// let mut bitmap = SmolBitmap::new();
    /// bitmap.insert(42);
    ///
    /// assert!(bitmap.get(42));
    /// assert!(!bitmap.get(43));
    /// assert!(!bitmap.get(1000)); // Out of bounds returns false
    /// ```
    #[must_use]
    #[inline]
    pub fn get(&self, i: usize) -> bool {
        // Check bounds
        if i >= self.capacity() {
            return false;
        }

        // For inline storage, check if bit index is beyond capacity
        let (idx, bp) = bitpos!(i);
        let slice = self.as_slice();
        debug_assert!(idx < slice.len(), "word index {idx} out of bounds");
        // SAFETY: We checked that idx < slice.len() above
        let word = unsafe { slice.get_unchecked(idx) };
        ((*word >> bp) & 1) != 0
    }

    /// Sets the bit at the given index to the specified value and returns the
    /// previous value.
    ///
    /// If the index is beyond the current capacity and the value is `true`,
    /// the bitmap will be resized to accommodate it. If the value is `false`
    /// and the index is out of bounds, no resize occurs and `false` is
    /// returned.
    ///
    /// # Examples
    ///
    /// ```
    /// # use smol_bitmap::SmolBitmap;
    /// let mut bitmap = SmolBitmap::new();
    ///
    /// assert_eq!(bitmap.replace(10, true), false);
    /// assert_eq!(bitmap.replace(10, false), true);
    /// assert_eq!(bitmap.replace(10, true), false);
    /// ```
    pub fn replace(&mut self, i: usize, v: bool) -> bool {
        self.replace_generic(i, v)
    }

    #[inline(always)]
    fn replace_generic(&mut self, i: usize, v: impl ToBool) -> bool {
        // Check if we need to grow
        let cap = self.capacity();
        if let Some(grow) = i.checked_sub(cap) {
            if !v.to_bool() {
                return false;
            }
            self.reserve(grow + 1);
        }

        // Compute word index and bit position
        let (idx, bp) = bitpos!(i);

        // Get a fresh slice after potential reallocation
        // SAFETY: reserve() ensures wi is within bounds of the slice
        let word = unsafe {
            let slice = self.as_mut_slice();
            // The word index should now be valid after reserve
            debug_assert!(
                idx < slice.len(),
                "word index {} >= slice len {}",
                idx,
                slice.len()
            );
            slice.get_unchecked_mut(idx)
        };

        let mask = 1 << bp;

        let prev = *word;
        if v.to_bool() {
            *word = prev | mask;
        } else {
            *word = prev & !mask;
        }
        (prev & mask) != 0
    }

    /// Sets the bit at the given index to the specified value.
    ///
    /// If the index is beyond the current capacity and the value is `true`,
    /// the bitmap will be resized to accommodate it.
    ///
    /// # Performance
    ///
    /// - O(1) for bits within current capacity
    /// - O(n) if reallocation is needed (when index > capacity)
    ///
    /// # Examples
    ///
    /// ```
    /// # use smol_bitmap::SmolBitmap;
    /// let mut bitmap = SmolBitmap::new();
    /// bitmap.insert(10);
    /// bitmap.insert(20);
    ///
    /// assert!(bitmap.get(10));
    /// assert!(bitmap.get(20));
    /// ```
    #[inline(always)]
    pub fn set(&mut self, i: usize, v: bool) {
        let _ = self.replace_generic(i, v);
    }

    /// Inserts a bit at the given index, setting it to `true`.
    ///
    /// Returns `true` if the bit was previously unset (insertion occurred),
    /// or `false` if it was already set.
    ///
    /// # Examples
    ///
    /// ```
    /// # use smol_bitmap::SmolBitmap;
    /// let mut bitmap = SmolBitmap::new();
    ///
    /// assert!(bitmap.insert(10)); // First insertion
    /// assert!(!bitmap.insert(10)); // Already set
    /// ```
    #[inline(always)]
    pub fn insert(&mut self, i: usize) -> bool {
        !self.replace_generic(i, True)
    }

    /// Removes a bit at the given index, setting it to `false`.
    ///
    /// Returns `true` if the bit was previously set (removal occurred),
    /// or `false` if it was already unset.
    ///
    /// # Examples
    ///
    /// ```
    /// # use smol_bitmap::SmolBitmap;
    /// let mut bitmap = SmolBitmap::new();
    /// bitmap.insert(10);
    ///
    /// assert!(bitmap.remove(10)); // Bit was set
    /// assert!(!bitmap.remove(10)); // Already unset
    /// ```
    #[inline(always)]
    pub fn remove(&mut self, i: usize) -> bool {
        self.replace_generic(i, False)
    }

    /// Clears all bits in the bitmap.
    ///
    /// This is equivalent to creating a new empty bitmap but it keeps
    /// the existing allocation if possible.
    ///
    /// # Examples
    ///
    /// ```
    /// # use smol_bitmap::SmolBitmap;
    /// let mut bitmap = SmolBitmap::new();
    /// bitmap.insert(100);
    /// bitmap.insert(200);
    ///
    /// bitmap.clear();
    /// assert!(!bitmap.get(100));
    /// assert!(bitmap.is_spilled());
    /// ```
    pub fn clear(&mut self) {
        if self.is_spilled() {
            // SAFETY: We checked that storage is spilled, so modifying the slice is safe
            unsafe { self.as_mut_slice().fill(0) };
        } else {
            self.array = [0; WORDS_INLINE];
        }
    }

    /// Shrinks the capacity of the bitmap as much as possible.
    ///
    /// This will remove trailing zero words and potentially move the data
    /// back to inline storage if it fits.
    ///
    /// # Examples
    ///
    /// ```
    /// # use smol_bitmap::SmolBitmap;
    /// let mut bitmap = SmolBitmap::new();
    /// bitmap.insert(300);
    /// bitmap.remove(300); // Clear the bit
    ///
    /// bitmap.shrink_to_fit();
    /// // May move back to inline storage if all set bits fit
    /// ```
    pub fn shrink_to_fit(&mut self) {
        self.update(
            #[inline(always)]
            |rb| {
                rb.shrink_to_fit();
            },
        );
    }

    /// Returns a trimmed slice of the bitmap, removing any trailing zero words.
    ///
    /// This method provides a view of the bitmap's underlying storage without
    /// trailing zeros, which can be useful for operations that require a
    /// compact representation of the set bits.
    ///
    /// # Returns
    ///
    /// A slice of type `&[u64]` representing the bitmap's storage without
    /// trailing zeros.
    ///
    /// # Examples
    ///
    /// ```
    /// use smol_bitmap::SmolBitmap;
    ///
    /// let mut bitmap = SmolBitmap::new();
    /// bitmap.insert(0);
    /// bitmap.insert(64);
    ///
    /// let trimmed_slice = bitmap.as_slice_rtrim();
    /// assert_eq!(trimmed_slice.len(), 2); // Only two words are needed
    /// ```
    pub const fn as_slice_rtrim(&self) -> &[u64] {
        rtrim0(self.as_slice())
    }

    /// Compares two slices for equivalency, ignoring trailing zero words.
    ///
    /// This function checks if two slices are equivalent by comparing their
    /// elements, ignoring any trailing zero words. This is useful for
    /// comparing bitmaps where trailing zeros do not affect the logical
    /// equivalence of the data.
    ///
    /// # Arguments
    ///
    /// * `a` - The first slice to compare.
    /// * `b` - The second slice to compare.
    ///
    /// # Returns
    ///
    /// `true` if the slices are equivalent when trailing zeros are ignored,
    /// `false` otherwise.
    ///
    /// # Examples
    ///
    /// ```
    /// use smol_bitmap::SmolBitmap;
    ///
    /// let a = SmolBitmap::from(&[1u64, 2, 0, 0]);
    /// let b = &[1u64, 2];
    /// assert!(a.eq_rtrim(b));
    ///
    /// let c = &[1u64, 2, 3];
    /// assert!(!a.eq_rtrim(c));
    /// ```
    pub fn eq_rtrim(&self, b: &[u64]) -> bool {
        let a = self.as_slice();
        let (a, b, common) = if a.len() >= b.len() {
            (a, b, b.len())
        } else {
            (b, a, a.len())
        };
        let (a, rem) = a.split_at(common);

        a == b && rem.iter().all(|&w| w == 0)
    }

    /// Compares two slices for ordering, ignoring trailing zero words.
    ///
    /// This function compares two slices by their elements, ignoring any
    /// trailing zero words. This is useful for comparing bitmaps where trailing
    /// zeros do not affect the logical ordering of the data.
    ///
    /// # Arguments
    ///
    /// * `a` - The first slice to compare.
    /// * `b` - The second slice to compare.
    ///
    /// # Returns
    ///
    /// An [`Ordering`] value that indicates whether `a` is less than, equal to,
    /// or greater than `b` when trailing zeros are ignored.
    ///
    /// # Examples
    ///
    /// ```
    /// use smol_bitmap::SmolBitmap;
    ///
    /// let a = SmolBitmap::from(&[1u64, 2, 0, 0]);
    /// let b = &[1u64, 2];
    /// assert_eq!(a.cmp_rtrim(b), core::cmp::Ordering::Equal);
    ///
    /// let c = &[1u64, 2, 3];
    /// assert_eq!(a.cmp_rtrim(c), core::cmp::Ordering::Less);
    /// ```
    pub fn cmp_rtrim(&self, b: &[u64]) -> Ordering {
        let a = self.as_slice();
        let (a, b, common, rev) = if a.len() >= b.len() {
            (a, b, b.len(), false)
        } else {
            (b, a, a.len(), true)
        };
        let (a, rem) = a.split_at(common);

        let result = a.cmp(b).then_with(|| {
            if rem.iter().all(|&w| w == 0) {
                cmp::Ordering::Equal
            } else {
                cmp::Ordering::Greater
            }
        });
        hint::select_unpredictable(rev, result.reverse(), result)
    }

    /// Removes a prefix of consecutive bits with the specified value.
    ///
    /// Efficiently removes all consecutive bits of the given value from the
    /// beginning of the bitmap by shifting the remaining bits left. This is
    /// useful for maintaining compact bitmap representations.
    ///
    /// # Algorithm
    ///
    /// 1. Skip whole words that match the pattern (all 0s or all 1s)
    /// 2. Find consecutive bits in the first non-matching word
    /// 3. Shift all remaining bits left by the total skip amount
    ///
    /// # Arguments
    ///
    /// * `bit` - The bit value to remove from the prefix (`true` for 1s,
    ///   `false` for 0s)
    ///
    /// # Returns
    ///
    /// The number of bits removed from the prefix.
    ///
    /// # Examples
    ///
    /// ```
    /// # use smol_bitmap::SmolBitmap;
    /// let mut bitmap = SmolBitmap::new();
    /// // Set bits: 111100101
    /// bitmap.insert(0);
    /// bitmap.insert(1);
    /// bitmap.insert(2);
    /// bitmap.insert(3);
    /// bitmap.insert(5);
    /// bitmap.insert(7);
    ///
    /// // Remove prefix of 1s
    /// let removed = bitmap.remove_prefix(true);
    /// assert_eq!(removed, 4); // Removed four leading 1s
    /// // Bitmap is now: 0101 (shifted left)
    /// ```
    pub fn remove_prefix(&mut self, bit: bool) -> usize {
        // First remove fully matching leading words
        // SAFETY: We're performing bit operations that don't affect storage mode
        let mut rb = unsafe { self.as_mut_slice() };
        let xor = if bit { !0 } else { 0 }; // Pattern to match (all 1s or all 0s)
        let word_skip = rb.iter().take_while(|&&w| w == xor).count();
        if word_skip > 0 {
            // Shift remaining words to the beginning
            rb.copy_within(word_skip.., 0);
            // Clear the tail that's now unused
            // SAFETY: word_skip <= rb.len() because it's from take_while on rb.iter()
            let (head, tail) = unsafe { rb.split_at_mut_unchecked(rb.len() - word_skip) };
            tail.fill(0);
            rb = head;
        }

        // Then remove consecutive bits from the first non-matching word
        let bit_skip = rb.first().map_or(0, |&w| (w ^ xor).trailing_zeros()) as usize;
        if bit_skip > 0 {
            // Shift all bits left by bit_skip positions
            let mut carry = 0;
            for word in rb.iter_mut().rev() {
                let v = *word;
                *word = (v >> bit_skip) | carry;
                carry = v << (64 - bit_skip);
            }
        }

        word_skip * 64 + bit_skip
    }

    /// Returns an iterator over the set bits.
    ///
    /// # Examples
    ///
    /// ```
    /// # use smol_bitmap::SmolBitmap;
    /// let mut bitmap = SmolBitmap::new();
    /// bitmap.insert(10);
    /// bitmap.insert(20);
    ///
    /// let mut iter = bitmap.iter();
    /// assert_eq!(iter.next(), Some(10));
    /// assert_eq!(iter.next(), Some(20));
    /// assert_eq!(iter.next(), None);
    /// ```
    #[must_use]
    pub const fn iter(&self) -> Iter<'_> {
        let slice = self.as_slice_rtrim();
        BitIter {
            words: slice,
            pos: 0,
            rpos: slice.len() * 64,
        }
    }

    /// Creates an iterator that selects elements from the provided iterator
    /// based on set bits.
    ///
    /// This method returns a `SelectIter` that filters the input iterator,
    /// yielding only elements at positions corresponding to set bits in the
    /// bitmap. This is useful for creating a subset of a collection based on
    /// a bitmap mask.
    ///
    /// # Arguments
    ///
    /// * `iter` - An iterator whose elements will be selected based on set bits
    ///
    /// # Examples
    ///
    /// ```
    /// # use smol_bitmap::SmolBitmap;
    /// let mut bitmap = SmolBitmap::new();
    /// bitmap.insert(0);
    /// bitmap.insert(2);
    /// bitmap.insert(4);
    ///
    /// let items = vec!["a", "b", "c", "d", "e"];
    /// let selected: Vec<_> = bitmap.select(items.iter().copied()).collect();
    /// assert_eq!(selected, vec!["a", "c", "e"]);
    /// ```
    #[must_use]
    pub fn select<I: IntoIterator>(&self, iter: I) -> SelectIter<'_, I::IntoIter> {
        SelectIter::new(self, iter)
    }

    /// Returns the number of set bits in the bitmap.
    ///
    /// Time complexity: O(n) where n is the number of words.
    ///
    /// # Examples
    ///
    /// ```
    /// # use smol_bitmap::SmolBitmap;
    /// let mut bitmap = SmolBitmap::new();
    /// assert_eq!(bitmap.len(), 0);
    ///
    /// bitmap.insert(10);
    /// bitmap.insert(20);
    /// assert_eq!(bitmap.len(), 2);
    /// ```
    #[must_use]
    #[inline]
    pub fn len(&self) -> usize {
        self.count_ones()
    }

    /// Returns the number of set bits below the given index.
    ///
    /// Counts all set bits at positions less than `idx`. This is useful for
    /// determining the position of an element in a compressed representation.
    ///
    /// Time complexity: O(w) where w is the number of words up to the target
    /// index.
    ///
    /// # Arguments
    ///
    /// * `idx` - The index to count below (exclusive upper bound)
    ///
    /// # Examples
    ///
    /// ```
    /// # use smol_bitmap::SmolBitmap;
    /// let mut bitmap = SmolBitmap::new();
    /// bitmap.insert(5);
    /// bitmap.insert(10);
    /// bitmap.insert(15);
    /// bitmap.insert(20);
    ///
    /// assert_eq!(bitmap.rank(0), 0); // No bits below index 0
    /// assert_eq!(bitmap.rank(6), 1); // Bit at index 5
    /// assert_eq!(bitmap.rank(12), 2); // Bits at indices 5, 10
    /// assert_eq!(bitmap.rank(25), 4); // All bits below index 25
    /// ```
    #[inline]
    #[must_use]
    pub fn rank(&self, i: usize) -> usize {
        let slice = self.as_slice();
        let (mut wrem, bit_idx) = bitpos!(i);

        let mut count = 0;
        for &word in slice {
            if wrem == 0 {
                // Create mask to include only bits below the target index
                let mask = (1u64 << bit_idx) - 1;
                count += (word & mask).count_ones() as usize;
                break;
            }

            // Count entire words before the target word
            count += word.count_ones() as usize;
            wrem -= 1;
        }
        count
    }

    /// Returns `true` if the bitmap contains no set bits.
    ///
    /// Time complexity: O(n) where n is the number of words.
    ///
    /// # Examples
    ///
    /// ```
    /// # use smol_bitmap::SmolBitmap;
    /// let mut bitmap = SmolBitmap::new();
    /// assert!(bitmap.is_empty());
    ///
    /// bitmap.insert(10);
    /// assert!(!bitmap.is_empty());
    /// ```
    #[must_use]
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.as_slice().iter().all(|w| *w == 0)
    }

    /// Returns the minimum (first) set bit in the bitmap, or [`None`] if the
    /// bitmap is empty.
    ///
    /// Time complexity: O(n) where n is the number of words.
    ///
    /// # Examples
    ///
    /// ```
    /// # use smol_bitmap::SmolBitmap;
    /// let mut bitmap = SmolBitmap::new();
    /// assert_eq!(bitmap.first(), None);
    ///
    /// bitmap.insert(10);
    /// bitmap.insert(5);
    /// bitmap.insert(20);
    /// assert_eq!(bitmap.first(), Some(5));
    /// ```
    #[inline]
    #[must_use]
    pub fn first(&self) -> Option<usize> {
        let slice = self.as_slice();
        for (wi, &word) in slice.iter().enumerate() {
            if word != 0 {
                let bi = word.trailing_zeros() as usize;
                return Some(wi * 64 + bi);
            }
        }
        None
    }

    /// Returns the maximum (last) set bit in the bitmap, or [`None`] if the
    /// bitmap is empty.
    ///
    /// Returns [`None`] if the bitmap is empty.
    ///
    /// Time complexity: O(n) where n is the number of words.
    ///
    /// # Examples
    ///
    /// ```
    /// # use smol_bitmap::SmolBitmap;
    /// let mut bitmap = SmolBitmap::new();
    /// assert_eq!(bitmap.last(), None);
    ///
    /// bitmap.insert(10);
    /// bitmap.insert(5);
    /// bitmap.insert(20);
    /// assert_eq!(bitmap.last(), Some(20));
    /// ```
    #[inline]
    #[must_use]
    pub fn last(&self) -> Option<usize> {
        let slice = self.as_slice();
        for (wi, &word) in slice.iter().enumerate().rev() {
            if word != 0 {
                let bi = 63 - word.leading_zeros() as usize;
                return Some(wi * 64 + bi);
            }
        }
        None
    }

    /// Counts the number of set bits in the bitmap.
    ///
    /// This method efficiently counts all set bits using the built-in
    /// `count_ones` method on each word.
    ///
    /// # Examples
    ///
    /// ```
    /// # use smol_bitmap::SmolBitmap;
    /// let mut bitmap = SmolBitmap::new();
    /// bitmap.insert(5);
    /// bitmap.insert(10);
    /// bitmap.insert(15);
    /// assert_eq!(bitmap.count_ones(), 3);
    /// ```
    #[inline]
    #[must_use]
    pub fn count_ones(&self) -> usize {
        self.as_slice()
            .iter()
            .map(|w| w.count_ones() as usize)
            .sum()
    }

    /// Counts the number of unset bits up to the capacity of the bitmap.
    ///
    /// # Examples
    ///
    /// ```
    /// # use smol_bitmap::SmolBitmap;
    /// let mut bitmap = SmolBitmap::new();
    /// bitmap.insert(5);
    /// bitmap.insert(10);
    /// let zeros = bitmap.count_zeros();
    /// assert_eq!(zeros, bitmap.capacity() - 2);
    /// ```
    #[must_use]
    pub fn count_zeros(&self) -> usize {
        let total_bits = self.capacity();
        total_bits - self.count_ones()
    }

    /// Complements the bit at the specified index.
    ///
    /// If the bit was set, it becomes unset. If it was unset, it becomes set.
    ///
    /// # Examples
    ///
    /// ```
    /// # use smol_bitmap::SmolBitmap;
    /// let mut bitmap = SmolBitmap::new();
    /// assert!(!bitmap.get(5));
    ///
    /// bitmap.complement(5);
    /// assert!(bitmap.get(5));
    ///
    /// bitmap.complement(5);
    /// assert!(!bitmap.get(5));
    /// ```
    #[inline]
    pub fn complement(&mut self, i: usize) -> bool {
        // Check if we need to grow
        let cap = self.capacity();
        if let Some(grow) = i.checked_sub(cap) {
            self.reserve(grow + 1);
        }

        // Compute word index and bit position
        let (idx, bp) = bitpos!(i);

        // Get a fresh slice after potential reallocation
        // SAFETY: reserve() ensures wi is within bounds of the slice
        let word = unsafe {
            let slice = self.as_mut_slice();
            // The word index should now be valid after reserve
            debug_assert!(
                idx < slice.len(),
                "word index {} >= slice len {}",
                idx,
                slice.len()
            );
            slice.get_unchecked_mut(idx)
        };

        let mask = 1 << bp;

        let prev = *word;
        *word = prev ^ mask;
        (prev & mask) != 0
    }

    /// Returns the index of the next set bit at or after the given index.
    ///
    /// If no set bit is found at or after the given index, returns `None`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use smol_bitmap::SmolBitmap;
    /// let mut bitmap = SmolBitmap::new();
    /// bitmap.insert(5);
    /// bitmap.insert(10);
    /// bitmap.insert(15);
    ///
    /// assert_eq!(bitmap.next_set_bit(0), Some(5));
    /// assert_eq!(bitmap.next_set_bit(6), Some(10));
    /// assert_eq!(bitmap.next_set_bit(11), Some(15));
    /// assert_eq!(bitmap.next_set_bit(16), None);
    /// ```
    #[inline]
    #[must_use]
    pub fn next_set_bit(&self, beg: usize) -> Option<usize> {
        if beg >= self.capacity() {
            return None;
        }
        let slice = self.as_slice();
        let cap = self.capacity();
        let (mut wi, bi) = bitpos!(beg);

        if wi >= slice.len() {
            return None;
        }

        // first partial word
        let mut w = slice[wi] & (!0u64 << bi);
        if w != 0 {
            let rel = w.trailing_zeros() as usize;
            let idx = wi * 64 + rel;
            return (idx < cap).then_some(idx);
        }
        wi += 1;

        // remaining words
        while wi < slice.len() {
            w = slice[wi];
            if w != 0 {
                let rel = w.trailing_zeros() as usize;
                let idx = wi * 64 + rel;
                return (idx < cap).then_some(idx);
            }
            wi += 1;
        }
        None
    }

    /// Returns the index of the previous set bit at or before the given index.
    ///
    /// If no set bit is found at or before the given index, returns `None`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use smol_bitmap::SmolBitmap;
    /// let mut bitmap = SmolBitmap::new();
    /// bitmap.insert(5);
    /// bitmap.insert(10);
    /// bitmap.insert(15);
    ///
    /// assert_eq!(bitmap.prev_set_bit(20), Some(15));
    /// assert_eq!(bitmap.prev_set_bit(14), Some(10));
    /// assert_eq!(bitmap.prev_set_bit(9), Some(5));
    /// assert_eq!(bitmap.prev_set_bit(4), None);
    /// ```
    #[inline]
    #[must_use]
    pub fn prev_set_bit(&self, from: usize) -> Option<usize> {
        if self.capacity() == 0 {
            return None;
        }
        let cap = self.capacity();
        let idx = from.min(cap - 1);
        let slice = self.as_slice();
        let (mut wi, bi) = bitpos!(idx);

        if wi >= slice.len() {
            if slice.is_empty() {
                return None;
            }
            wi = slice.len() - 1;
        }

        // first partial word
        let mask = if bi == 63 {
            !0u64
        } else {
            (1u64 << (bi + 1)) - 1
        };
        let mut w = slice[wi] & mask;
        if w != 0 {
            let pos = 63 - w.leading_zeros() as usize;
            return Some(wi * 64 + pos);
        }

        // previous words
        while wi > 0 {
            wi -= 1;
            w = slice[wi];
            if w != 0 {
                let pos = 63 - w.leading_zeros() as usize;
                return Some(wi * 64 + pos);
            }
        }
        None
    }

    // ========================================================================
    // Shift Operations
    // ========================================================================

    /// Shifts all bits left by `n` positions.
    ///
    /// Bits that would be shifted beyond the capacity are lost.
    ///
    /// # Examples
    ///
    /// ```
    /// use smol_bitmap::SmolBitmap;
    ///
    /// let mut bitmap = SmolBitmap::new();
    /// bitmap.insert(0);
    /// bitmap.insert(1);
    /// bitmap.insert(2);
    ///
    /// let shifted = bitmap.shl(2);
    /// assert!(!shifted.get(0));
    /// assert!(!shifted.get(1));
    /// assert!(shifted.get(2));
    /// assert!(shifted.get(3));
    /// assert!(shifted.get(4));
    /// ```
    #[must_use]
    pub fn shl(&self, n: usize) -> Self {
        if n == 0 {
            return self.clone();
        }

        let slice = self.as_slice_rtrim();
        if slice.is_empty() {
            return Self::new();
        }

        // Calculate shift amounts
        let word_shift = n >> 6; // n / 64
        let shift = (n & 63) as u32; // n % 64

        // Calculate result size - find highest set bit and add shift
        let last_bit = self.last().unwrap_or(0);
        let result_bits = last_bit + n + 1;
        let result_words = result_bits.div_ceil(64);

        let mut builder = SmolBitmapBuilder::with_capacity(result_words);

        // Add leading zeros for word shift
        for _ in 0..word_shift {
            builder.push(0);
        }

        if shift == 0 {
            // Simple case: just copy words
            builder.extend_from_slice(slice);
        } else {
            // Complex case: shift within words
            let mut carry = 0u64;
            for &word in slice {
                builder.push(carry | (word << shift));
                carry = word.wrapping_shr(shift.wrapping_neg());
            }
            if carry != 0 {
                builder.push(carry);
            }
        }

        builder.into()
    }

    /// Shifts all bits right by `n` positions.
    ///
    /// Bits that would be shifted below 0 are lost.
    ///
    /// # Examples
    ///
    /// ```
    /// use smol_bitmap::SmolBitmap;
    ///
    /// let mut bitmap = SmolBitmap::new();
    /// bitmap.insert(2);
    /// bitmap.insert(3);
    /// bitmap.insert(4);
    ///
    /// let shifted = bitmap.shr(2);
    /// assert!(shifted.get(0));
    /// assert!(shifted.get(1));
    /// assert!(shifted.get(2));
    /// assert!(!shifted.get(3));
    /// assert!(!shifted.get(4));
    /// ```
    #[must_use]
    pub fn shr(&self, n: usize) -> Self {
        if n == 0 {
            return self.clone();
        }

        let slice = self.as_slice_rtrim();
        if slice.is_empty() {
            return Self::new();
        }

        // Skip words that will be shifted out completely
        let (word_shift, shift) = bitpos!(n);
        let shift = shift as u32;
        if word_shift >= slice.len() {
            return Self::new();
        }

        let remaining_words = slice.len() - word_shift;
        let mut builder = SmolBitmapBuilder::with_capacity(remaining_words);

        if shift == 0 {
            // Simple case: just copy words from offset
            builder.extend_from_slice(&slice[word_shift..]);
        } else {
            builder.resize(remaining_words, 0);
            let output = builder.as_mut_slice();

            let mut carry = 0u64;
            for (output, &input) in output.iter_mut().zip(&slice[word_shift..]).rev() {
                *output = input >> shift | carry;
                carry = input.wrapping_shl(shift.wrapping_neg());
            }
        }

        builder.into()
    }

    // ========================================================================
    // Convenience Methods
    // ========================================================================

    /// Counts the number of leading zero bits (from bit 0 upward).
    ///
    /// Returns `None` if the bitmap is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use smol_bitmap::SmolBitmap;
    ///
    /// let mut bitmap = SmolBitmap::new();
    /// assert_eq!(bitmap.leading_zeros(), None);
    ///
    /// bitmap.insert(3);
    /// assert_eq!(bitmap.leading_zeros(), Some(3));
    ///
    /// bitmap.insert(0);
    /// assert_eq!(bitmap.leading_zeros(), Some(0));
    /// ```
    #[must_use]
    pub fn leading_zeros(&self) -> Option<usize> {
        self.first()
    }

    /// Counts the number of trailing zero bits (from the highest set bit
    /// downward).
    ///
    /// Returns `None` if the bitmap is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use smol_bitmap::SmolBitmap;
    ///
    /// let mut bitmap = SmolBitmap::new();
    /// bitmap.insert(3);
    /// bitmap.insert(5);
    /// bitmap.insert(10);
    ///
    /// // 4 trailing zeros from bit 10 down to bit 6 (bit 5 is set)
    /// assert_eq!(bitmap.trailing_zeros(), Some(4));
    /// ```
    #[must_use]
    pub fn trailing_zeros(&self) -> Option<usize> {
        let last = self.last()?;
        match self.prev_set_bit(last.saturating_sub(1)) {
            Some(prev) => Some(last - prev - 1),
            None => Some(last), // All bits below 'last' are zero
        }
    }

    /// Counts the number of leading one bits (consecutive ones from bit 0).
    ///
    /// # Examples
    ///
    /// ```
    /// use smol_bitmap::SmolBitmap;
    ///
    /// let mut bitmap = SmolBitmap::new();
    /// bitmap.insert(0);
    /// bitmap.insert(1);
    /// bitmap.insert(2);
    /// bitmap.insert(4);
    ///
    /// assert_eq!(bitmap.leading_ones(), 3);
    /// ```
    #[must_use]
    pub fn leading_ones(&self) -> usize {
        let slice = self.as_slice();
        let mut total = 0usize;

        for &w in slice {
            if w == !0 {
                total += 64;
            } else {
                // Found a word with at least one zero
                return total + w.trailing_ones() as usize;
            }
        }

        // All words are all ones, but cap at capacity
        total.min(self.capacity())
    }

    /// Counts the number of trailing one bits (consecutive ones from the
    /// highest set bit).
    ///
    /// # Examples
    ///
    /// ```
    /// use smol_bitmap::SmolBitmap;
    ///
    /// let mut bitmap = SmolBitmap::new();
    /// bitmap.insert(2);
    /// bitmap.insert(4);
    /// bitmap.insert(5);
    /// bitmap.insert(6);
    ///
    /// assert_eq!(bitmap.trailing_ones(), 3);
    /// ```
    #[must_use]
    pub fn trailing_ones(&self) -> usize {
        let slice = self.as_slice();
        let Some(last_bit) = self.last() else {
            return 0;
        };

        let wi = last_bit >> 6;
        let bi = last_bit & 63;
        let mut count = 0usize;

        // Count down from highest bit within the last word
        let hi = slice[wi];
        count += (hi << (63 - bi)).leading_ones() as usize;

        // Then whole preceding words of all-ones
        let mut i = wi;
        while i > 0 {
            i -= 1;
            if slice[i] == !0 {
                count += 64;
            } else {
                // Found a word with at least one zero
                count += slice[i].leading_ones() as usize;
                break;
            }
        }
        count
    }

    // ========================================================================
    // Find/Count Methods
    // ========================================================================

    /// Finds the first unset bit in the bitmap.
    ///
    /// Returns `None` if all bits up to capacity are set.
    ///
    /// # Examples
    ///
    /// ```
    /// use smol_bitmap::SmolBitmap;
    ///
    /// let mut bitmap = SmolBitmap::new();
    /// assert_eq!(bitmap.find_first_zero(), Some(0));
    ///
    /// bitmap.insert(0);
    /// bitmap.insert(1);
    /// bitmap.insert(3);
    /// assert_eq!(bitmap.find_first_zero(), Some(2));
    /// ```
    #[must_use]
    pub fn find_first_zero(&self) -> Option<usize> {
        let slice = self.as_slice();
        let cap = self.capacity();

        for (wi, &word) in slice.iter().enumerate() {
            if word != !0 {
                let zeros = !word;
                let bi = zeros.trailing_zeros() as usize;
                let idx = wi * 64 + bi;
                if idx < cap {
                    return Some(idx);
                }
            }
        }
        None
    }

    /// Finds the last unset bit in the bitmap.
    ///
    /// Returns `None` if all bits are set or the bitmap is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use smol_bitmap::SmolBitmap;
    ///
    /// let mut bitmap = SmolBitmap::new();
    /// bitmap.insert(0);
    /// bitmap.insert(2);
    /// bitmap.insert(5);
    ///
    /// // The last unset bit before bit 5
    /// assert_eq!(bitmap.find_last_zero(), Some(4));
    /// ```
    #[must_use]
    pub fn find_last_zero(&self) -> Option<usize> {
        // Find the maximum bit to search up to
        let max_bit = if let Some(last) = self.last() {
            last
        } else {
            return Some(0); // Empty bitmap, first bit is zero
        };

        // Use find_prev_zero to scan from max_bit
        self.find_prev_zero(max_bit)
    }

    /// Finds the next unset bit at or after the given position.
    ///
    /// Returns `None` if no unset bit is found within capacity.
    ///
    /// # Examples
    ///
    /// ```
    /// use smol_bitmap::SmolBitmap;
    ///
    /// let mut bitmap = SmolBitmap::new();
    /// bitmap.insert(0);
    /// bitmap.insert(1);
    /// bitmap.insert(3);
    ///
    /// assert_eq!(bitmap.find_next_zero(0), Some(2));
    /// assert_eq!(bitmap.find_next_zero(2), Some(2));
    /// assert_eq!(bitmap.find_next_zero(3), Some(4));
    /// ```
    #[must_use]
    pub fn find_next_zero(&self, beg: usize) -> Option<usize> {
        if beg >= self.capacity() {
            return None;
        }

        let (mut wi, bi) = bitpos!(beg);
        let slice = self.as_slice();

        // Check the first word (partial)
        if wi < slice.len() {
            let word = slice[wi];
            // Mask off bits before 'from'
            let mask = !0u64 << bi;
            let masked = word | !mask;
            if masked != !0 {
                let zeros = !masked;
                let rel = zeros.trailing_zeros() as usize;
                return Some(wi * 64 + rel);
            }
            wi += 1;
        }

        // Check remaining words
        while wi < slice.len() {
            let word = slice[wi];
            if word != !0 {
                let zeros = !word;
                let bi = zeros.trailing_zeros() as usize;
                let idx = wi * 64 + bi;
                if idx < self.capacity() {
                    return Some(idx);
                }
            }
            wi += 1;
        }

        None
    }

    /// Finds the previous unset bit at or before the given position.
    ///
    /// Returns `None` if no unset bit is found.
    ///
    /// # Examples
    ///
    /// ```
    /// use smol_bitmap::SmolBitmap;
    ///
    /// let mut bitmap = SmolBitmap::new();
    /// bitmap.insert(1);
    /// bitmap.insert(3);
    /// bitmap.insert(5);
    ///
    /// assert_eq!(bitmap.find_prev_zero(5), Some(4));
    /// assert_eq!(bitmap.find_prev_zero(3), Some(2));
    /// assert_eq!(bitmap.find_prev_zero(1), Some(0));
    /// ```
    #[must_use]
    pub fn find_prev_zero(&self, from: usize) -> Option<usize> {
        let from = from.min(self.capacity().saturating_sub(1));
        let (mut wi, bi) = bitpos!(from);
        let slice = self.as_slice();

        // Check the first word (partial)
        if wi < slice.len() {
            let word = slice[wi];
            // Mask to only consider bits up to and including 'from'
            let mask = if bi == 63 {
                !0u64
            } else {
                (1u64 << (bi + 1)) - 1
            };
            let masked = word & mask;

            if masked != mask {
                // There's at least one zero bit
                // Find the highest zero bit by inverting and finding leading one
                let zeros = !masked & mask;
                let highest_zero = 63 - zeros.leading_zeros() as usize;
                return Some(wi * 64 + highest_zero);
            }
        }

        // Check previous words
        while wi > 0 {
            wi -= 1;
            let word = slice[wi];
            if word != !0 {
                // Find the highest zero bit
                let zeros = !word;
                let highest_zero = 63 - zeros.leading_zeros() as usize;
                return Some(wi * 64 + highest_zero);
            }
        }

        None
    }

    /// Counts the number of set bits in the range [beg, end).
    ///
    /// # Examples
    ///
    /// ```
    /// use smol_bitmap::SmolBitmap;
    ///
    /// let mut bitmap = SmolBitmap::new();
    /// bitmap.insert(1);
    /// bitmap.insert(3);
    /// bitmap.insert(5);
    /// bitmap.insert(7);
    ///
    /// assert_eq!(bitmap.count_ones_range(0, 4), 2); // bits 1 and 3
    /// assert_eq!(bitmap.count_ones_range(2, 8), 3); // bits 3, 5, and 7
    /// ```
    #[must_use]
    pub fn count_ones_range(&self, beg: usize, end: usize) -> usize {
        if beg >= end {
            return 0;
        }

        let mut count = 0;
        let slice = self.as_slice();
        let (beg_wi, beg_bi) = bitpos!(beg);
        let (end_wi, end_bi) = bitpos!(end);

        if beg_wi == end_wi {
            // Range within single word
            if beg_wi < slice.len() {
                let mask = ((1u64 << (end_bi - beg_bi)) - 1) << beg_bi;
                count = (slice[beg_wi] & mask).count_ones() as usize;
            }
        } else {
            // First word (partial)
            if beg_wi < slice.len() {
                let mask = !0u64 << beg_bi;
                count += (slice[beg_wi] & mask).count_ones() as usize;
            }

            // Middle words (full)
            count += slice
                .iter()
                .take(end_wi)
                .skip(beg_wi + 1)
                .map(|&item| item.count_ones() as usize)
                .sum::<usize>();

            // Last word (partial)
            if end_wi < slice.len() && end_bi > 0 {
                let mask = (1u64 << end_bi) - 1;
                count += (slice[end_wi] & mask).count_ones() as usize;
            }
        }

        count
    }

    /// Counts the number of unset bits in the range [beg, end).
    ///
    /// # Examples
    ///
    /// ```
    /// use smol_bitmap::SmolBitmap;
    ///
    /// let mut bitmap = SmolBitmap::new();
    /// bitmap.insert(1);
    /// bitmap.insert(3);
    ///
    /// assert_eq!(bitmap.count_zeros_range(0, 4), 2); // bits 0 and 2
    /// assert_eq!(bitmap.count_zeros_range(0, 8), 6); // 8 - 2 set bits
    /// ```
    #[must_use]
    pub fn count_zeros_range(&self, beg: usize, end: usize) -> usize {
        if beg >= end {
            return 0;
        }

        let range_size = end - beg;
        let ones = self.count_ones_range(beg, end);
        range_size - ones
    }

    // ========================================================================
    // Batch Operations
    // ========================================================================

    /// Sets all bits up to the current highest set bit to true.
    ///
    /// # Examples
    ///
    /// ```
    /// use smol_bitmap::SmolBitmap;
    ///
    /// let mut bitmap = SmolBitmap::new();
    /// bitmap.insert(0);
    /// bitmap.insert(5);
    ///
    /// bitmap.set_all();
    /// assert!(bitmap.get(0));
    /// assert!(bitmap.get(1));
    /// assert!(bitmap.get(2));
    /// assert!(bitmap.get(3));
    /// assert!(bitmap.get(4));
    /// assert!(bitmap.get(5));
    /// ```
    pub fn set_all(&mut self) {
        if let Some(end) = self.last() {
            let (last_word_idx, last_bit_idx) = bitpos!(end);
            // SAFETY: We're setting bits within the valid range
            unsafe {
                let slice = self.as_mut_slice();

                // Set complete words to all 1s
                if last_word_idx > 0 {
                    slice[..last_word_idx].fill(!0);
                }

                // Set partial last word
                if last_word_idx < slice.len() {
                    slice[last_word_idx] |= (1u64 << (last_bit_idx + 1)) - 1;
                }
            }
        }
    }

    /// Clears bits in the range [beg, end).
    ///
    /// # Panics
    ///
    /// Panics if beg > end.
    ///
    /// # Examples
    ///
    /// ```
    /// use smol_bitmap::SmolBitmap;
    ///
    /// let mut bitmap = SmolBitmap::new();
    /// for i in 0..10 {
    ///     bitmap.insert(i);
    /// }
    ///
    /// bitmap.clear_range(3, 7);
    /// assert!(bitmap.get(2));
    /// assert!(!bitmap.get(3));
    /// assert!(!bitmap.get(6));
    /// assert!(bitmap.get(7));
    /// ```
    pub fn clear_range(&mut self, beg: usize, end: usize) {
        debug_assert!(beg <= end, "beg must be <= end");

        let (beg_wi, beg_bi) = bitpos!(beg);
        let (end_wi, end_bi) = bitpos!(end);

        // SAFETY: We're clearing bits within valid range
        unsafe {
            let slice = self.as_mut_slice();

            if beg_wi == end_wi {
                // Range within single word
                if beg_wi < slice.len() {
                    let mask = ((1u64 << (end_bi - beg_bi)) - 1) << beg_bi;
                    slice[beg_wi] &= !mask;
                }
            } else {
                // First word (partial)
                if beg_wi < slice.len() {
                    let mask = !0u64 << beg_bi;
                    slice[beg_wi] &= !mask;
                }

                // Middle words (full)
                let end = end_wi.min(slice.len());
                if beg_wi + 1 < end {
                    slice[beg_wi + 1..end].fill(0);
                }

                // Last word (partial)
                if end_wi < slice.len() && end_bi > 0 {
                    let mask = (1u64 << end_bi) - 1;
                    slice[end_wi] &= !mask;
                }
            }
        }
    }

    /// Complements all bits in the range [beg, end).
    ///
    /// # Panics
    ///
    /// Panics if beg > end.
    ///
    /// # Examples
    ///
    /// ```
    /// use smol_bitmap::SmolBitmap;
    ///
    /// let mut bitmap = SmolBitmap::new();
    /// bitmap.insert(2);
    /// bitmap.insert(4);
    ///
    /// bitmap.complement_range(1, 6);
    ///
    /// assert!(bitmap.get(1));
    /// assert!(!bitmap.get(2));
    /// assert!(bitmap.get(3));
    /// assert!(!bitmap.get(4));
    /// assert!(bitmap.get(5));
    /// ```
    pub fn complement_range(&mut self, beg: usize, end: usize) {
        debug_assert!(beg <= end, "beg must be <= end");

        let (beg_wi, beg_bi) = bitpos!(beg);
        let (end_wi, end_bi) = bitpos!(end);

        // SAFETY: We're complementing bits within valid range
        unsafe {
            let slice = self.as_mut_slice();

            if beg_wi == end_wi {
                // Range within single word
                if beg_wi < slice.len() {
                    let mask = ((1u64 << (end_bi - beg_bi)) - 1) << beg_bi;
                    slice[beg_wi] ^= mask;
                }
            } else {
                // First word (partial)
                if beg_wi < slice.len() {
                    let mask = !0u64 << beg_bi;
                    slice[beg_wi] ^= mask;
                }

                // Middle words (full)
                let end = end_wi.min(slice.len());
                if beg_wi + 1 < end {
                    for word in &mut slice[beg_wi + 1..end] {
                        *word = !*word;
                    }
                }

                // Last word (partial)
                if end_wi < slice.len() && end_bi > 0 {
                    let mask = (1u64 << end_bi) - 1;
                    slice[end_wi] ^= mask;
                }
            }
        }
    }

    /// Sets all bits bits in the range [beg, end).
    ///
    /// # Panics
    ///
    /// Panics if beg > end.
    ///
    /// # Examples
    ///
    /// ```
    /// use smol_bitmap::SmolBitmap;
    ///
    /// let mut bitmap = SmolBitmap::new();
    /// bitmap.set_range(2, 6);
    ///
    /// assert!(!bitmap.get(1));
    /// assert!(bitmap.get(2));
    /// assert!(bitmap.get(4));
    /// assert!(bitmap.get(5));
    /// assert!(!bitmap.get(6));
    /// ```
    pub fn set_range(&mut self, beg: usize, end: usize) {
        debug_assert!(beg <= end, "beg must be <= end");

        let (beg_wi, beg_bi) = bitpos!(beg);
        let (end_wi, end_bi) = bitpos!(end);

        // SAFETY: We're clearing bits within valid range
        unsafe {
            let slice = self.as_mut_slice();

            if beg_wi == end_wi {
                // Range within single word
                if beg_wi < slice.len() {
                    let mask = ((1u64 << (end_bi - beg_bi)) - 1) << beg_bi;
                    slice[beg_wi] |= mask;
                }
            } else {
                // First word (partial)
                if beg_wi < slice.len() {
                    let mask = !0u64 << beg_bi;
                    slice[beg_wi] |= mask;
                }

                // Middle words (full)
                let end = end_wi.min(slice.len());
                if beg_wi + 1 < end {
                    slice[beg_wi + 1..end].fill(!0);
                }

                // Last word (partial)
                if end_wi < slice.len() && end_bi > 0 {
                    let mask = (1u64 << end_bi) - 1;
                    slice[end_wi] |= mask;
                }
            }
        }
    }

    /// Sets all bits in the range [beg, end) to the specified value.
    ///
    /// # Examples
    ///
    /// ```
    /// use smol_bitmap::SmolBitmap;
    ///
    /// let mut bitmap = SmolBitmap::new();
    ///
    /// bitmap.set_range_value(5, 10, true);
    /// assert!(!bitmap.get(4));
    /// assert!(bitmap.get(5));
    /// assert!(bitmap.get(9));
    /// assert!(!bitmap.get(10));
    ///
    /// bitmap.set_range_value(7, 9, false);
    /// assert!(bitmap.get(6));
    /// assert!(!bitmap.get(7));
    /// assert!(!bitmap.get(8));
    /// assert!(bitmap.get(9));
    /// ```
    pub fn set_range_value(&mut self, beg: usize, end: usize, value: bool) {
        if beg >= end {
            return;
        }

        let (beg_wi, beg_bi) = bitpos!(beg);
        let (end_wi, end_bi) = bitpos!(end);

        // SAFETY: We're clearing bits within valid range
        unsafe {
            let slice = self.as_mut_slice();

            if beg_wi == end_wi {
                // Range within single word
                if beg_wi < slice.len() {
                    let mask = ((1u64 << (end_bi - beg_bi)) - 1) << beg_bi;
                    if value {
                        slice[beg_wi] |= mask;
                    } else {
                        slice[beg_wi] &= !mask;
                    }
                }
            } else {
                // First word (partial)
                if beg_wi < slice.len() {
                    let mask = !0u64 << beg_bi;
                    if value {
                        slice[beg_wi] |= mask;
                    } else {
                        slice[beg_wi] &= !mask;
                    }
                }

                // Middle words (full)
                let filler = if value { !0 } else { 0 };
                let end = end_wi.min(slice.len());
                if beg_wi + 1 < end {
                    slice[beg_wi + 1..end].fill(filler);
                }

                // Last word (partial)
                if end_wi < slice.len() && end_bi > 0 {
                    let mask = (1u64 << end_bi) - 1;
                    if value {
                        slice[end_wi] |= mask;
                    } else {
                        slice[end_wi] &= !mask;
                    }
                }
            }
        }
    }

    /// Sets all bits up to capacity to the specified value.
    ///
    /// # Examples
    ///
    /// ```
    /// use smol_bitmap::SmolBitmap;
    ///
    /// let mut bitmap = SmolBitmap::new();
    /// bitmap.insert(10); // This determines a capacity
    ///
    /// bitmap.fill(true);
    /// // All bits from 0 to 10 are now true
    /// for i in 0..=10 {
    ///     assert!(bitmap.get(i));
    /// }
    /// ```
    pub fn fill(&mut self, value: bool) {
        if value {
            // Set all bits to true up to the max set bit (or capacity)
            if let Some(end) = self.last() {
                let (last_word_idx, last_bit_idx) = bitpos!(end);
                // SAFETY: We're setting bits within the valid range
                unsafe {
                    let slice = self.as_mut_slice();

                    // Set complete words to all 1s
                    if last_word_idx > 0 {
                        slice[..last_word_idx].fill(!0);
                    }

                    // Set partial last word
                    if last_word_idx < slice.len() {
                        slice[last_word_idx] |= (1u64 << (last_bit_idx + 1)) - 1;
                    }
                }
            }
        } else {
            // Clear all bits
            self.clear();
        }
    }

    // ========================================================================
    // Range Operations
    // ========================================================================

    /// Extracts bits in the range [beg, end) as a u64 value.
    ///
    /// Returns up to 64 bits. If the range is larger than 64 bits, only the
    /// first 64 bits are returned.
    ///
    /// # Panics
    ///
    /// Panics if beg > end.
    ///
    /// # Examples
    ///
    /// ```
    /// use smol_bitmap::SmolBitmap;
    ///
    /// let mut bitmap = SmolBitmap::new();
    /// bitmap.insert(0);
    /// bitmap.insert(2);
    /// bitmap.insert(3);
    ///
    /// // Extract bits 0-4: 1101 in binary = 13 in decimal
    /// assert_eq!(bitmap.get_range(0, 4), 0b1101);
    /// ```
    #[must_use]
    pub fn get_range(&self, beg: usize, end: usize) -> u64 {
        debug_assert!(beg <= end, "beg must be <= end");

        let len = (end - beg).min(64);
        if len == 0 {
            return 0;
        }

        let slice = self.as_slice();
        let (w0, b0) = bitpos!(beg);
        if w0 >= slice.len() {
            return 0;
        }

        if b0 + len <= 64 {
            let mask = (!0u64 >> (64 - len)) << b0;
            (slice[w0] & mask) >> b0
        } else {
            let lo_bits = 64 - b0;
            let hi_bits = len - lo_bits;
            let lo = (slice[w0] >> b0) & ((1u64 << lo_bits) - 1);
            let hi = if w0 + 1 < slice.len() {
                slice[w0 + 1] & ((1u64 << hi_bits) - 1)
            } else {
                0
            };
            lo | (hi << lo_bits)
        }
    }

    /// Extracts a 64-bit word at the given word index.
    ///
    /// This method returns the word at the specified index. For inline storage,
    /// if reading the last word (index 1), bit 127 (the MSB) is cleared to hide
    /// the storage mode indicator.
    ///
    /// # Arguments
    ///
    /// * `word_idx` - The word index to extract (0-based)
    ///
    /// # Examples
    ///
    /// ```
    /// use smol_bitmap::SmolBitmap;
    ///
    /// let mut bitmap = SmolBitmap::new();
    /// bitmap.insert(0);
    /// bitmap.insert(63);
    /// bitmap.insert(64);
    /// bitmap.insert(126);
    ///
    /// assert_eq!(bitmap.extract_word(0), (1u64 << 63) | 1);
    /// assert_eq!(bitmap.extract_word(1), (1u64 << 62) | 1); // bit 127 is masked
    /// ```
    #[inline]
    #[must_use]
    pub fn extract_word(&self, word_idx: usize) -> u64 {
        *self.as_slice().get(word_idx).unwrap_or(&0)
    }

    /// Inserts a 64-bit word at the given word index.
    ///
    /// This method sets the word at the specified index. If the bitmap is using
    /// inline storage and bit 127 would be set (MSB of the last word), the
    /// bitmap is automatically promoted to heap storage.
    ///
    /// # Arguments
    ///
    /// * `word_idx` - The word index to write to (0-based)
    /// * `word` - The 64-bit word to insert
    ///
    /// # Examples
    ///
    /// ```
    /// use smol_bitmap::SmolBitmap;
    ///
    /// let mut bitmap = SmolBitmap::new();
    ///
    /// // Set word 0
    /// bitmap.put_word(0, 0xFFFF_FFFF_FFFF_FFFF);
    /// assert!(!bitmap.is_spilled());
    ///
    /// // Setting MSB of word 1 causes promotion to heap
    /// bitmap.put_word(1, 0x8000_0000_0000_0000);
    /// assert!(bitmap.is_spilled());
    /// ```
    #[inline]
    pub fn put_word(&mut self, word_idx: usize, word: u64) {
        let dst = match (self.is_spilled(), word_idx, word) {
            // External & Within Capacity
            (true, i, _) => unsafe { self.as_mut_slice().get_mut(i) },
            // Inline & Cannot affect MSB
            (false, 0, _) => self.array.get_mut(0),
            // Inline & Does not affect MSB
            (false, 1, w) if !msb!(w) => self.array.get_mut(1),
            // Out of bounds
            (false, _, _) => None,
        };
        if let Some(p) = dst {
            *p = word;
            return;
        }

        self.update(|rb| {
            // Ensure we have capacity for this word
            rb.extend_to(word_idx + 1, 0);

            // Set the word
            // SAFETY: We've checked that word_idx is within bounds
            unsafe { *rb.get_unchecked_mut(word_idx) = word };
        });
    }

    /// Resizes the bitmap to contain exactly `new_bits` bits.
    ///
    /// If `new_bits` is greater than the current capacity, the bitmap is
    /// extended with zeros. If `new_bits` is less than the current
    /// capacity, the bitmap is truncated.
    ///
    /// # Arguments
    ///
    /// * `new_bits` - The new size in bits
    ///
    /// # Examples
    ///
    /// ```
    /// use smol_bitmap::SmolBitmap;
    ///
    /// let mut bitmap = SmolBitmap::new();
    /// bitmap.insert(50);
    /// bitmap.insert(100);
    ///
    /// // Resize to 75 bits - bit 100 will be removed
    /// bitmap.resize(75);
    /// assert!(bitmap.get(50));
    /// assert!(!bitmap.get(100));
    ///
    /// // Resize to 200 bits - expands with zeros
    /// bitmap.resize(200);
    /// assert!(bitmap.is_spilled()); // Beyond inline capacity
    /// ```
    pub fn resize(&mut self, new_bits: usize) {
        let current_capacity = self.capacity();

        if new_bits == current_capacity {
            return;
        }

        if new_bits > current_capacity {
            // Expanding - just reserve the additional capacity
            self.reserve(new_bits - current_capacity);
        } else {
            // Shrinking - truncate to the new size
            self.truncate(new_bits);
        }
    }

    /// Truncates the bitmap to contain at most `max_bits` bits.
    ///
    /// If `max_bits` is greater than or equal to the current highest set bit,
    /// this has no effect. Otherwise, all bits at positions >= `max_bits` are
    /// cleared.
    ///
    /// This method may also shrink the storage if the truncation allows the
    /// bitmap to fit back into inline storage.
    ///
    /// # Arguments
    ///
    /// * `max_bits` - The maximum number of bits to keep
    ///
    /// # Examples
    ///
    /// ```
    /// use smol_bitmap::SmolBitmap;
    ///
    /// let mut bitmap = SmolBitmap::new();
    /// bitmap.insert(50);
    /// bitmap.insert(100);
    /// bitmap.insert(150);
    ///
    /// // Truncate to 120 bits - bit 150 will be removed
    /// bitmap.truncate(120);
    /// assert!(bitmap.get(50));
    /// assert!(bitmap.get(100));
    /// assert!(!bitmap.get(150));
    ///
    /// // Further truncation
    /// bitmap.truncate(60);
    /// assert!(bitmap.get(50));
    /// assert!(!bitmap.get(100));
    /// ```
    pub fn truncate(&mut self, max_bits: usize) {
        if max_bits == 0 {
            self.clear();
            return;
        }

        let (last_word_idx, last_bit_idx) = bitpos!(max_bits - 1);
        let (used, discard) = unsafe { self.as_mut_slice().split_at_mut(last_word_idx + 1) };
        discard.fill(0);

        // Clear the high bits in the last word if needed
        if last_bit_idx < 63 {
            let mask = (1u64 << (last_bit_idx + 1)) - 1;
            used[last_word_idx] &= mask;
        }
    }
}

// ============================================================================
// Index Trait Implementations
// ============================================================================

impl Index<usize> for SmolBitmap {
    type Output = bool;

    /// Returns a reference to a static bool representing the bit at the given
    /// index.
    ///
    /// Note: Since we can't return a reference to a bit directly, this returns
    /// a reference to a static `true` or `false` value based on the bit state.
    ///
    /// Returns `false` for indices beyond the capacity, consistent with
    /// `get()`.
    ///
    /// # Examples
    ///
    /// ```
    /// use core::ops::Index;
    /// use smol_bitmap::SmolBitmap;
    ///
    /// let mut bitmap = SmolBitmap::new();
    /// bitmap.insert(5);
    ///
    /// assert_eq!(*bitmap.index(5), true);
    /// assert_eq!(*bitmap.index(0), false);
    /// assert_eq!(*bitmap.index(1000), false); // Out of bounds returns false
    /// ```
    fn index(&self, index: usize) -> &Self::Output {
        if self.get(index) { &true } else { &false }
    }
}

/// Helper method to extract a range of bits as a new bitmap.
///
/// This is the actual implementation for range extraction, since the Index
/// trait requires returning a reference which doesn't work well for computed
/// values.
impl SmolBitmap {
    /// Extracts a range of bits as a new bitmap.
    ///
    /// The bits in the range [start, end) are copied to a new bitmap,
    /// with bit `start` becoming bit 0 in the new bitmap.
    ///
    /// # Examples
    ///
    /// ```
    /// use smol_bitmap::SmolBitmap;
    ///
    /// let mut bitmap = SmolBitmap::new();
    /// bitmap.insert(2);
    /// bitmap.insert(3);
    /// bitmap.insert(5);
    ///
    /// let sub = bitmap.bitslice(2, 6);
    /// assert!(sub.get(0)); // bit 2 -> 0
    /// assert!(sub.get(1)); // bit 3 -> 1
    /// assert!(!sub.get(2)); // bit 4 -> 2
    /// assert!(sub.get(3)); // bit 5 -> 3
    /// ```
    #[must_use]
    pub fn bitslice(&self, beg: usize, end: usize) -> Self {
        let end = end.min(self.capacity());
        let bits = match end.checked_sub(beg) {
            None | Some(0) => return Self::new(),
            Some(bits) => bits,
        };
        let n = bits.div_ceil(64); // exact # of words in the RESULT
        let mut buf = SmolBitmapBuilder::with_capacity(n);

        let (wi, bi) = bitpos!(beg);
        let slice = self.as_slice();
        if bi == 0 {
            // Word-aligned: copy exactly the words we need.
            buf.extend_from_slice(&slice[wi..wi + n]);
        } else {
            // Misaligned: each output word is (v0 >> s) | (v1 << (64 - s)).
            let out = buf.spare_capacity_mut();
            let shift = bi as u32;
            let ishift = shift.wrapping_neg() & 63;

            let input = &slice[wi..wi + n];
            let output = &mut out[..n];
            let mut carry = slice.get(wi + n).unwrap_or(&0) << ishift;

            for (output, &input) in output.iter_mut().zip(input).rev() {
                output.write((input >> shift) | carry);
                carry = input << ishift;
            }

            unsafe {
                buf.set_len(n);
            }
        }

        // Mask the final partial word to the exact bit-width of the range.
        let rem = bits & 63;
        if rem != 0 {
            let last = buf.as_mut_slice().last_mut().unwrap();
            *last &= (1u64 << rem) - 1;
        }

        buf.into()
    }

    /// Extracts bits from the given position to the end as a new bitmap.
    ///
    /// # Examples
    ///
    /// ```
    /// use smol_bitmap::SmolBitmap;
    ///
    /// let mut bitmap = SmolBitmap::new();
    /// bitmap.insert(2);
    /// bitmap.insert(3);
    /// bitmap.insert(5);
    ///
    /// let sub = bitmap.skip(2);
    /// assert!(sub.get(0)); // bit 2 -> 0
    /// assert!(sub.get(1)); // bit 3 -> 1
    /// assert!(sub.get(3)); // bit 5 -> 3
    /// ```
    #[must_use]
    pub fn skip(&self, beg: usize) -> Self {
        self.shr(beg)
    }

    /// Extracts bits from the beginning up to (but not including) the given
    /// position.
    ///
    /// # Examples
    ///
    /// ```
    /// use smol_bitmap::SmolBitmap;
    ///
    /// let mut bitmap = SmolBitmap::new();
    /// bitmap.insert(1);
    /// bitmap.insert(3);
    /// bitmap.insert(5);
    ///
    /// let sub = bitmap.take(4);
    /// assert!(sub.get(1));
    /// assert!(sub.get(3));
    /// assert!(!sub.get(5)); // Not included
    /// ```
    #[must_use]
    pub fn take(&self, end: usize) -> Self {
        let end = end.min(self.capacity());
        if end == 0 {
            return Self::new();
        }

        let (last_word_idx, last_bit_idx) = bitpos!(end - 1);

        // Clear all words beyond the last needed word
        let words_needed = last_word_idx + 1;
        let source = self.as_slice();
        let mut rb = SmolBitmapBuilder::from_slice(&source[..words_needed]);

        // Clear the high bits in the last word if needed
        if last_word_idx < rb.len() && last_bit_idx < 63 {
            let mask = (1u64 << (last_bit_idx + 1)) - 1;
            rb[last_word_idx] &= mask;
        }

        // Try to shrink back to inline storage if possible
        rb.into()
    }
}

/// A trait to convert types to a boolean value.
///
/// This trait is used to allow the [`replace_generic`] method to be
/// monomorphized with a constant parameter, enabling compile-time
/// optimizations while still supporting runtime flexibility. It is
/// particularly useful for implementing methods like `insert` and
/// `remove` in the [`SmolBitmap`] struct, where the boolean value
/// can be determined at compile time for efficiency.
trait ToBool: Copy {
    /// Converts the implementing type to a boolean value.
    fn to_bool(self) -> bool;
}

/// A marker type representing the boolean value `true`.
#[derive(Copy, Clone)]
struct True;

/// A marker type representing the boolean value `false`.
#[derive(Copy, Clone)]
struct False;

impl ToBool for True {
    #[inline(always)]
    fn to_bool(self) -> bool {
        true
    }
}

impl ToBool for False {
    #[inline(always)]
    fn to_bool(self) -> bool {
        false
    }
}

impl ToBool for bool {
    #[inline(always)]
    fn to_bool(self) -> bool {
        self
    }
}
