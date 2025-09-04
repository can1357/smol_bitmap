//! `SmolBitmap` struct and core implementation.

use alloc::vec::Vec;
use core::{mem, ops::Index, slice};

use crate::{
    iter::{BitIter, Iter, SelectIter},
    storage::{
        ArrayBitmap, BITS_INLINE, BitArray, SmolBitmapBuilder, WORDS_INLINE, bitpos, rtrim0,
    },
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
/// - **Inline**: Up to SmolBitmap::inline_capacity() bits stored directly in
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
/// bitmap.set(10, true);
/// bitmap.set(100, true);
///
/// // Check bits
/// assert!(bitmap.get(10));
/// assert!(bitmap.get(100));
/// assert!(!bitmap.get(50)); // Unset bits are false
///
/// // Force heap allocation
/// bitmap.set(200, true);
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
    /// bitmap.set(1, true);
    /// bitmap.set(2, true);
    /// bitmap.set(5, true);
    /// bitmap.set(8, true);
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
    /// bitmap.set(200, true); // Beyond inline capacity
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
        if n <= 0 {
            panic!("external word count should be positive")
        }
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
    pub fn as_mut_ptr(&mut self) -> *mut u64 {
        if self.is_spilled() {
            self.external_ptr()
        } else {
            self.array.as_mut_ptr()
        }
    }

    /// Get the storage as a slice
    #[must_use]
    pub fn as_slice(&self) -> &[u64] {
        unsafe { slice::from_raw_parts(self.as_ptr(), self.word_count()) }
    }

    /// Get the storage as a mutable slice
    /// # Safety
    /// The caller must ensure that:
    /// - If the storage is inline, the MSB of the last word must not be set
    /// - Modifications must maintain the storage invariants
    /// - The slice must not be extended beyond its capacity
    #[inline(always)]
    pub unsafe fn as_mut_slice(&mut self) -> &mut [u64] {
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
    /// The closure `f` receives a mutable reference to BitArray and can modify
    /// it. This pattern ensures:
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
    /// bitmap.set(42, true);
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
        let (idx, bp) = bitpos(i);
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
    /// assert_eq!(bitmap.exchange(10, true), false);
    /// assert_eq!(bitmap.exchange(10, false), true);
    /// assert_eq!(bitmap.exchange(10, true), false);
    /// ```
    #[inline(always)]
    pub fn exchange(&mut self, i: usize, v: bool) -> bool {
        // Check if we need to grow
        let cap = self.capacity();
        if let Some(grow) = i.checked_sub(cap) {
            if !v {
                return false;
            }
            self.reserve(grow + 1);
        }

        // Compute word index and bit position
        let (idx, bp) = bitpos(i);

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
        if v {
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
    /// bitmap.set(10, true);
    /// bitmap.set(20, true);
    ///
    /// assert!(bitmap.get(10));
    /// assert!(bitmap.get(20));
    /// ```
    #[inline(always)]
    pub fn set(&mut self, i: usize, v: bool) {
        let _ = self.exchange(i, v);
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
        !self.exchange(i, true)
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
    /// bitmap.set(10, true);
    ///
    /// assert!(bitmap.remove(10)); // Bit was set
    /// assert!(!bitmap.remove(10)); // Already unset
    /// ```
    #[inline(always)]
    pub fn remove(&mut self, i: usize) -> bool {
        self.exchange(i, false)
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
    /// bitmap.set(100, true);
    /// bitmap.set(200, true);
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
    /// bitmap.set(300, true);
    /// bitmap.set(300, false); // Clear the bit
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

    /// Returns the trimmed slice of the bitmap.
    pub(crate) fn as_slice_rtrim(&self) -> &[u64] {
        rtrim0(self.as_slice())
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
    /// bitmap.set(0, true);
    /// bitmap.set(1, true);
    /// bitmap.set(2, true);
    /// bitmap.set(3, true);
    /// bitmap.set(5, true);
    /// bitmap.set(7, true);
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
    /// bitmap.set(10, true);
    /// bitmap.set(20, true);
    ///
    /// let mut iter = bitmap.iter();
    /// assert_eq!(iter.next(), Some(10));
    /// assert_eq!(iter.next(), Some(20));
    /// assert_eq!(iter.next(), None);
    /// ```
    #[must_use]
    pub fn iter(&self) -> Iter<'_> {
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
    /// bitmap.set(0, true);
    /// bitmap.set(2, true);
    /// bitmap.set(4, true);
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
    /// bitmap.set(10, true);
    /// bitmap.set(20, true);
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
    /// bitmap.set(5, true);
    /// bitmap.set(10, true);
    /// bitmap.set(15, true);
    /// bitmap.set(20, true);
    ///
    /// assert_eq!(bitmap.position_of(0), 0); // No bits below index 0
    /// assert_eq!(bitmap.position_of(6), 1); // Bit at index 5
    /// assert_eq!(bitmap.position_of(12), 2); // Bits at indices 5, 10
    /// assert_eq!(bitmap.position_of(25), 4); // All bits below index 25
    /// ```
    #[inline]
    #[must_use]
    pub fn position_of(&self, idx: usize) -> usize {
        let slice = self.as_slice();
        let (mut wrem, bit_idx) = bitpos(idx);

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
    /// bitmap.set(10, true);
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
    /// bitmap.set(10, true);
    /// bitmap.set(5, true);
    /// bitmap.set(20, true);
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
    /// bitmap.set(10, true);
    /// bitmap.set(5, true);
    /// bitmap.set(20, true);
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
    /// bitmap.set(5, true);
    /// bitmap.set(10, true);
    /// bitmap.set(15, true);
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
    /// bitmap.set(5, true);
    /// bitmap.set(10, true);
    /// let zeros = bitmap.count_zeros();
    /// assert_eq!(zeros, bitmap.capacity() - 2);
    /// ```
    #[must_use]
    pub fn count_zeros(&self) -> usize {
        let total_bits = self.capacity();
        total_bits - self.count_ones()
    }

    /// Flips all bits in the bitmap up to the specified bit index.
    ///
    /// This creates a new bitmap where each bit from 0 to `max_bit` (inclusive)
    /// is inverted. Bits beyond `max_bit` are not included in the result.
    ///
    /// # Examples
    ///
    /// ```
    /// # use smol_bitmap::SmolBitmap;
    /// let mut bitmap = SmolBitmap::new();
    /// bitmap.set(1, true);
    /// bitmap.set(3, true);
    ///
    /// let flipped = bitmap.complement(4);
    /// assert!(flipped.get(0)); // Was false, now true
    /// assert!(!flipped.get(1)); // Was true, now false
    /// assert!(flipped.get(2)); // Was false, now true
    /// assert!(!flipped.get(3)); // Was true, now false
    /// assert!(flipped.get(4)); // Was false, now true
    /// ```
    #[must_use]
    pub fn complement(&self, max_bit: usize) -> Self {
        let mut result = Self::with_capacity(max_bit + 1);
        let (last_word_idx, last_bit_idx) = bitpos(max_bit);

        result.update(|rb| {
            let self_slice = self.as_slice();
            let num_words = last_word_idx + 1;

            // Ensure we have enough capacity - need at least WORDS_MINEXT for external
            // storage
            if num_words > rb.len() {
                rb.extend_to(num_words, !0);
            } else {
                // Already have enough capacity, just fill what we need
                for i in 0..num_words {
                    rb[i] = !0;
                }
            }

            // Apply NOT operation word by word
            for i in 0..num_words.min(self_slice.len()) {
                rb[i] = !self_slice[i];
            }

            // For words beyond self's length, they're already all 1s from fill above

            // Mask the last word to only include bits up to max_bit
            if last_word_idx < rb.len() {
                let mask = if last_bit_idx == 63 {
                    !0u64
                } else {
                    (1u64 << (last_bit_idx + 1)) - 1
                };
                rb[last_word_idx] &= mask;
            }
        });

        result
    }

    /// Toggles the bit at the specified index.
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
    /// bitmap.toggle(5);
    /// assert!(bitmap.get(5));
    ///
    /// bitmap.toggle(5);
    /// assert!(!bitmap.get(5));
    /// ```
    #[inline]
    pub fn toggle(&mut self, i: usize) {
        let current = self.get(i);
        self.set(i, !current);
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
    /// bitmap.set(5, true);
    /// bitmap.set(10, true);
    /// bitmap.set(15, true);
    ///
    /// assert_eq!(bitmap.next_set_bit(0), Some(5));
    /// assert_eq!(bitmap.next_set_bit(6), Some(10));
    /// assert_eq!(bitmap.next_set_bit(11), Some(15));
    /// assert_eq!(bitmap.next_set_bit(16), None);
    /// ```
    #[inline]
    #[must_use]
    pub fn next_set_bit(&self, from: usize) -> Option<usize> {
        if from >= self.capacity() {
            return None;
        }
        let slice = self.as_slice();
        let cap = self.capacity();
        let (mut wi, bi) = bitpos(from);

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
    /// bitmap.set(5, true);
    /// bitmap.set(10, true);
    /// bitmap.set(15, true);
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
        let (mut wi, bi) = bitpos(idx);

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
    /// bitmap.set(0, true);
    /// bitmap.set(1, true);
    /// bitmap.set(2, true);
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
        let bit_shift = n & 63; // n % 64

        // Calculate result size - find highest set bit and add shift
        let last_bit = self.last().unwrap_or(0);
        let result_bits = last_bit + n + 1;
        let result_words = result_bits.div_ceil(64);

        let mut builder = SmolBitmapBuilder::with_capacity(result_words);

        // Add leading zeros for word shift
        for _ in 0..word_shift {
            builder.push(0);
        }

        if bit_shift == 0 {
            // Simple case: just copy words
            builder.extend_from_slice(slice);
        } else {
            // Complex case: shift within words
            let mut carry = 0u64;
            for &word in slice {
                builder.push(carry | (word << bit_shift));
                carry = word >> (64 - bit_shift);
            }
            if carry != 0 {
                builder.push(carry);
            }
        }

        builder.finalize()
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
    /// bitmap.set(2, true);
    /// bitmap.set(3, true);
    /// bitmap.set(4, true);
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

        // Calculate shift amounts
        let word_shift = n >> 6; // n / 64
        let bit_shift = n & 63; // n % 64

        // Skip words that will be shifted out completely
        if word_shift >= slice.len() {
            return Self::new();
        }

        let remaining_words = slice.len() - word_shift;
        let mut builder = SmolBitmapBuilder::with_capacity(remaining_words);

        if bit_shift == 0 {
            // Simple case: just copy words from offset
            builder.extend_from_slice(&slice[word_shift..]);
        } else {
            // Complex case: shift within words
            let shifted_slice = &slice[word_shift..];
            for i in 0..shifted_slice.len() {
                let low_bits = shifted_slice[i] >> bit_shift;
                let high_bits = if i + 1 < shifted_slice.len() {
                    shifted_slice[i + 1] << (64 - bit_shift)
                } else {
                    0
                };
                builder.push(low_bits | high_bits);
            }
        }

        builder.finalize()
    }

    // ========================================================================
    // Convenience Methods
    // ========================================================================

    /// Returns `true` if any bit is set.
    ///
    /// This is equivalent to `!self.is_empty()`.
    ///
    /// # Examples
    ///
    /// ```
    /// use smol_bitmap::SmolBitmap;
    ///
    /// let mut bitmap = SmolBitmap::new();
    /// assert!(!bitmap.any());
    ///
    /// bitmap.set(42, true);
    /// assert!(bitmap.any());
    /// ```
    #[inline]
    #[must_use]
    pub fn any(&self) -> bool {
        !self.is_empty()
    }

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
    /// bitmap.set(3, true);
    /// assert_eq!(bitmap.leading_zeros(), Some(3));
    ///
    /// bitmap.set(0, true);
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
    /// bitmap.set(3, true);
    /// bitmap.set(5, true);
    /// bitmap.set(10, true);
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
    /// bitmap.set(0, true);
    /// bitmap.set(1, true);
    /// bitmap.set(2, true);
    /// bitmap.set(4, true);
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
    /// bitmap.set(2, true);
    /// bitmap.set(4, true);
    /// bitmap.set(5, true);
    /// bitmap.set(6, true);
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
    /// bitmap.set(0, true);
    /// bitmap.set(1, true);
    /// bitmap.set(3, true);
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
    /// bitmap.set(0, true);
    /// bitmap.set(2, true);
    /// bitmap.set(5, true);
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
    /// bitmap.set(0, true);
    /// bitmap.set(1, true);
    /// bitmap.set(3, true);
    ///
    /// assert_eq!(bitmap.find_next_zero(0), Some(2));
    /// assert_eq!(bitmap.find_next_zero(2), Some(2));
    /// assert_eq!(bitmap.find_next_zero(3), Some(4));
    /// ```
    #[must_use]
    pub fn find_next_zero(&self, from: usize) -> Option<usize> {
        if from >= self.capacity() {
            return None;
        }

        let (mut wi, bi) = bitpos(from);
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
    /// bitmap.set(1, true);
    /// bitmap.set(3, true);
    /// bitmap.set(5, true);
    ///
    /// assert_eq!(bitmap.find_prev_zero(5), Some(4));
    /// assert_eq!(bitmap.find_prev_zero(3), Some(2));
    /// assert_eq!(bitmap.find_prev_zero(1), Some(0));
    /// ```
    #[must_use]
    pub fn find_prev_zero(&self, from: usize) -> Option<usize> {
        let from = from.min(self.capacity().saturating_sub(1));
        let (mut wi, bi) = bitpos(from);
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

    /// Counts the number of set bits in the range [start, end).
    ///
    /// # Examples
    ///
    /// ```
    /// use smol_bitmap::SmolBitmap;
    ///
    /// let mut bitmap = SmolBitmap::new();
    /// bitmap.set(1, true);
    /// bitmap.set(3, true);
    /// bitmap.set(5, true);
    /// bitmap.set(7, true);
    ///
    /// assert_eq!(bitmap.count_ones_range(0, 4), 2); // bits 1 and 3
    /// assert_eq!(bitmap.count_ones_range(2, 8), 3); // bits 3, 5, and 7
    /// ```
    #[must_use]
    pub fn count_ones_range(&self, start: usize, end: usize) -> usize {
        if start >= end {
            return 0;
        }

        let mut count = 0;
        let slice = self.as_slice();
        let (start_wi, start_bi) = bitpos(start);
        let (end_wi, end_bi) = bitpos(end);

        if start_wi == end_wi {
            // Range within single word
            if start_wi < slice.len() {
                let mask = ((1u64 << (end_bi - start_bi)) - 1) << start_bi;
                count = (slice[start_wi] & mask).count_ones() as usize;
            }
        } else {
            // First word (partial)
            if start_wi < slice.len() {
                let mask = !0u64 << start_bi;
                count += (slice[start_wi] & mask).count_ones() as usize;
            }

            // Middle words (full)
            count += slice
                .iter()
                .take(end_wi)
                .skip(start_wi + 1)
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

    /// Counts the number of unset bits in the range [start, end).
    ///
    /// # Examples
    ///
    /// ```
    /// use smol_bitmap::SmolBitmap;
    ///
    /// let mut bitmap = SmolBitmap::new();
    /// bitmap.set(1, true);
    /// bitmap.set(3, true);
    ///
    /// assert_eq!(bitmap.count_zeros_range(0, 4), 2); // bits 0 and 2
    /// assert_eq!(bitmap.count_zeros_range(0, 8), 6); // 8 - 2 set bits
    /// ```
    #[must_use]
    pub fn count_zeros_range(&self, start: usize, end: usize) -> usize {
        if start >= end {
            return 0;
        }

        let range_size = end - start;
        let ones = self.count_ones_range(start, end);
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
    /// bitmap.set(0, true);
    /// bitmap.set(5, true);
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
        if let Some(max_bit) = self.last() {
            let (last_word_idx, last_bit_idx) = bitpos(max_bit);
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

    /// Clears bits in the range [start, end).
    ///
    /// # Panics
    ///
    /// Panics if start > end.
    ///
    /// # Examples
    ///
    /// ```
    /// use smol_bitmap::SmolBitmap;
    ///
    /// let mut bitmap = SmolBitmap::new();
    /// for i in 0..10 {
    ///     bitmap.set(i, true);
    /// }
    ///
    /// bitmap.clear_range(3, 7);
    /// assert!(bitmap.get(2));
    /// assert!(!bitmap.get(3));
    /// assert!(!bitmap.get(6));
    /// assert!(bitmap.get(7));
    /// ```
    pub fn clear_range(&mut self, start: usize, end: usize) {
        debug_assert!(start <= end, "start must be <= end");

        let (start_wi, start_bi) = bitpos(start);
        let (end_wi, end_bi) = bitpos(end);

        // SAFETY: We're clearing bits within valid range
        unsafe {
            let slice = self.as_mut_slice();

            if start_wi == end_wi {
                // Range within single word
                if start_wi < slice.len() {
                    let mask = ((1u64 << (end_bi - start_bi)) - 1) << start_bi;
                    slice[start_wi] &= !mask;
                }
            } else {
                // First word (partial)
                if start_wi < slice.len() {
                    let mask = !0u64 << start_bi;
                    slice[start_wi] &= !mask;
                }

                // Middle words (full)
                let end = end_wi.min(slice.len());
                if start_wi + 1 < end {
                    slice[start_wi + 1..end].fill(0);
                }

                // Last word (partial)
                if end_wi < slice.len() && end_bi > 0 {
                    let mask = (1u64 << end_bi) - 1;
                    slice[end_wi] &= !mask;
                }
            }
        }
    }

    /// Sets all bits bits in the range [start, end).
    ///
    /// # Panics
    ///
    /// Panics if start > end.
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
    pub fn set_range(&mut self, start: usize, end: usize) {
        debug_assert!(start <= end, "start must be <= end");

        let (start_wi, start_bi) = bitpos(start);
        let (end_wi, end_bi) = bitpos(end);

        // SAFETY: We're clearing bits within valid range
        unsafe {
            let slice = self.as_mut_slice();

            if start_wi == end_wi {
                // Range within single word
                if start_wi < slice.len() {
                    let mask = ((1u64 << (end_bi - start_bi)) - 1) << start_bi;
                    slice[start_wi] |= mask;
                }
            } else {
                // First word (partial)
                if start_wi < slice.len() {
                    let mask = !0u64 << start_bi;
                    slice[start_wi] |= mask;
                }

                // Middle words (full)
                let end = end_wi.min(slice.len());
                if start_wi + 1 < end {
                    slice[start_wi + 1..end].fill(!0);
                }

                // Last word (partial)
                if end_wi < slice.len() && end_bi > 0 {
                    let mask = (1u64 << end_bi) - 1;
                    slice[end_wi] |= mask;
                }
            }
        }
    }

    /// Sets all bits in the range [start, end) to the specified value.
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
    pub fn set_range_value(&mut self, start: usize, end: usize, value: bool) {
        if start >= end {
            return;
        }

        let (start_wi, start_bi) = bitpos(start);
        let (end_wi, end_bi) = bitpos(end);

        // SAFETY: We're clearing bits within valid range
        unsafe {
            let slice = self.as_mut_slice();

            if start_wi == end_wi {
                // Range within single word
                if start_wi < slice.len() {
                    let mask = ((1u64 << (end_bi - start_bi)) - 1) << start_bi;
                    if value {
                        slice[start_wi] |= mask;
                    } else {
                        slice[start_wi] &= !mask;
                    }
                }
            } else {
                // First word (partial)
                if start_wi < slice.len() {
                    let mask = !0u64 << start_bi;
                    if value {
                        slice[start_wi] |= mask;
                    } else {
                        slice[start_wi] &= !mask;
                    }
                }

                // Middle words (full)
                let filler = if value { !0 } else { 0 };
                let end = end_wi.min(slice.len());
                if start_wi + 1 < end {
                    slice[start_wi + 1..end].fill(filler);
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
    /// bitmap.set(10, true); // This determines a capacity
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
            if let Some(max_bit) = self.last() {
                let (last_word_idx, last_bit_idx) = bitpos(max_bit);
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
    // Bytes Conversion
    // ========================================================================

    /// Converts the bitmap to little-endian bytes.
    ///
    /// # Examples
    ///
    /// ```
    /// use smol_bitmap::SmolBitmap;
    ///
    /// let mut bitmap = SmolBitmap::new();
    /// bitmap.set(0, true);
    /// bitmap.set(7, true);
    /// bitmap.set(8, true);
    ///
    /// let bytes = bitmap.to_bytes_le();
    /// assert_eq!(bytes[0], 0b10000001); // bits 0 and 7
    /// assert_eq!(bytes[1], 0b00000001); // bit 8
    /// ```
    #[must_use]
    pub fn to_bytes_le(&self) -> Vec<u8> {
        let slice = self.as_slice_rtrim();
        let mut bytes = Vec::with_capacity(slice.len() * 8);
        if slice.is_empty() {
            return bytes;
        }

        for &word in slice {
            bytes.extend_from_slice(&word.to_le_bytes());
        }

        // Trim trailing zeros
        while bytes.last() == Some(&0) {
            bytes.pop();
        }

        bytes
    }

    /// Converts the bitmap to big-endian bytes.
    ///
    /// # Examples
    ///
    /// ```
    /// use smol_bitmap::SmolBitmap;
    ///
    /// let mut bitmap = SmolBitmap::new();
    /// bitmap.set(0, true);
    /// bitmap.set(7, true);
    ///
    /// let bytes = bitmap.to_bytes_be();
    /// // Big-endian representation
    /// ```
    #[must_use]
    pub fn to_bytes_be(&self) -> Vec<u8> {
        let slice = self.as_slice_rtrim();
        let mut bytes = Vec::with_capacity(slice.len() * 8);
        if slice.is_empty() {
            return bytes;
        }

        // Process words in reverse order for big-endian
        for &word in slice.iter().rev() {
            bytes.extend_from_slice(&word.to_be_bytes());
        }

        // Find first non-zero byte and remove leading zeros in one pass
        if let Some(first_nz) = bytes.iter().position(|&b| b != 0) {
            bytes.drain(..first_nz);
        } else {
            bytes.clear(); // All zeros
        }

        bytes
    }

    /// Constructs a bitmap from little-endian bytes.
    ///
    /// # Examples
    ///
    /// ```
    /// use smol_bitmap::SmolBitmap;
    ///
    /// let bytes = vec![0b10000001, 0b00000001];
    /// let bitmap = SmolBitmap::from_bytes_le(&bytes);
    ///
    /// assert!(bitmap.get(0)); // bit 0 from byte 0
    /// assert!(bitmap.get(7)); // bit 7 from byte 0
    /// assert!(bitmap.get(8)); // bit 0 from byte 1
    /// ```
    #[must_use]
    pub fn from_bytes_le(bytes: &[u8]) -> Self {
        if bytes.is_empty() {
            return Self::new();
        }

        let mut words = SmolBitmapBuilder::with_capacity(bytes.len().div_ceil(8));

        let (chunks, rest) = bytes.as_chunks();
        for chunk in chunks {
            words.push(u64::from_le_bytes(*chunk));
        }
        if !rest.is_empty() {
            let mut word_bytes = [0u8; 8];
            word_bytes[..rest.len()].copy_from_slice(rest);
            words.push(u64::from_le_bytes(word_bytes));
        }

        words.finalize()
    }

    /// Constructs a bitmap from big-endian bytes.
    ///
    /// # Examples
    ///
    /// ```
    /// use smol_bitmap::SmolBitmap;
    ///
    /// let bytes = vec![0x01, 0x00]; // Big-endian representation
    /// let bitmap = SmolBitmap::from_bytes_be(&bytes);
    ///
    /// assert!(bitmap.get(8)); // The high bit of the first byte
    /// ```
    #[must_use]
    pub fn from_bytes_be(bytes: &[u8]) -> Self {
        if bytes.is_empty() {
            return Self::new();
        }

        // Process bytes in chunks of 8 (word size)
        let mut words = SmolBitmapBuilder::with_capacity(bytes.len().div_ceil(8));

        // Process from the end for big-endian
        let mut remaining = bytes;
        while !remaining.is_empty() {
            let chunk_size = remaining.len().min(8);
            let start = remaining.len() - chunk_size;
            let chunk = &remaining[start..];

            let mut word_bytes = [0u8; 8];
            // Right-align the bytes in the word
            word_bytes[(8 - chunk_size)..].copy_from_slice(chunk);
            words.push(u64::from_be_bytes(word_bytes));

            remaining = &remaining[..start];
        }

        // Push words in reverse order (since we processed from the end)
        words.as_mut_slice().reverse();
        words.finalize()
    }

    // ========================================================================
    // Range Operations
    // ========================================================================

    /// Extracts bits in the range [start, end) as a u64 value.
    ///
    /// Returns up to 64 bits. If the range is larger than 64 bits, only the
    /// first 64 bits are returned.
    ///
    /// # Panics
    ///
    /// Panics if start > end.
    ///
    /// # Examples
    ///
    /// ```
    /// use smol_bitmap::SmolBitmap;
    ///
    /// let mut bitmap = SmolBitmap::new();
    /// bitmap.set(0, true);
    /// bitmap.set(2, true);
    /// bitmap.set(3, true);
    ///
    /// // Extract bits 0-4: 1101 in binary = 13 in decimal
    /// assert_eq!(bitmap.get_range(0, 4), 0b1101);
    /// ```
    #[must_use]
    pub fn get_range(&self, start: usize, end: usize) -> u64 {
        debug_assert!(start <= end, "start must be <= end");

        let len = (end - start).min(64);
        if len == 0 {
            return 0;
        }

        let slice = self.as_slice();
        let (w0, b0) = bitpos(start);
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
    /// bitmap.set(5, true);
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
    /// bitmap.set(2, true);
    /// bitmap.set(3, true);
    /// bitmap.set(5, true);
    ///
    /// let sub = bitmap.get_range_bitmap(2, 6);
    /// assert!(sub.get(0)); // bit 2 -> 0
    /// assert!(sub.get(1)); // bit 3 -> 1
    /// assert!(!sub.get(2)); // bit 4 -> 2
    /// assert!(sub.get(3)); // bit 5 -> 3
    /// ```
    #[must_use]
    pub fn get_range_bitmap(&self, start: usize, end: usize) -> Self {
        let mut result = Self::new();

        if start >= end {
            return result;
        }

        for (new_idx, old_idx) in (start..end).enumerate() {
            if self.get(old_idx) {
                result.set(new_idx, true);
            }
        }

        result
    }

    /// Extracts bits from the given position to the end as a new bitmap.
    ///
    /// # Examples
    ///
    /// ```
    /// use smol_bitmap::SmolBitmap;
    ///
    /// let mut bitmap = SmolBitmap::new();
    /// bitmap.set(2, true);
    /// bitmap.set(3, true);
    /// bitmap.set(5, true);
    ///
    /// let sub = bitmap.get_from(2);
    /// assert!(sub.get(0)); // bit 2 -> 0
    /// assert!(sub.get(1)); // bit 3 -> 1
    /// assert!(sub.get(3)); // bit 5 -> 3
    /// ```
    #[must_use]
    pub fn get_from(&self, start: usize) -> Self {
        let mut result = Self::new();

        for bit in self.iter() {
            if bit >= start {
                result.set(bit - start, true);
            }
        }

        result
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
    /// bitmap.set(1, true);
    /// bitmap.set(3, true);
    /// bitmap.set(5, true);
    ///
    /// let sub = bitmap.get_to(4);
    /// assert!(sub.get(1));
    /// assert!(sub.get(3));
    /// assert!(!sub.get(5)); // Not included
    /// ```
    #[must_use]
    pub fn get_to(&self, end: usize) -> Self {
        let slice = self.as_slice();
        let (end_wi, end_bi) = bitpos(end);

        // Calculate how many words we need
        let words_needed = if end_bi == 0 { end_wi } else { end_wi + 1 };
        let copy_words = words_needed.min(slice.len());

        let mut builder = SmolBitmapBuilder::with_capacity(copy_words);

        if end_wi >= slice.len() {
            // Copy all words since end is beyond our data
            builder.extend_from_slice(slice);
        } else if end_bi == 0 {
            // End aligns with word boundary - copy whole words
            builder.extend_from_slice(&slice[..end_wi]);
        } else {
            // Copy whole words first
            builder.extend_from_slice(&slice[..end_wi]);

            // Mask and copy the final partial word if it exists
            if end_wi < slice.len() {
                let mask = (1u64 << end_bi) - 1;
                builder.push(slice[end_wi] & mask);
            }
        }

        builder.finalize()
    }
}
