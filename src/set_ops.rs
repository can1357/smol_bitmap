//! Implementations of set operations for `SmolBitmap`.

use crate::{SmolBitmap, storage::bitpos};

impl SmolBitmap {
    /// Performs a bitwise OR operation with another bitmap.
    ///
    /// This sets each bit in `self` to `self[i] | other[i]`. If `other`
    /// is larger, the bitmap is extended to accommodate all bits.
    ///
    /// # Examples
    ///
    /// ```
    /// # use smol_bitmap::SmolBitmap;
    /// let mut a = SmolBitmap::new();
    /// let mut b = SmolBitmap::new();
    ///
    /// a.set(10, true);
    /// b.set(20, true);
    ///
    /// a.union_with(&b);
    /// assert!(a.get(10));
    /// assert!(a.get(20));
    /// ```
    pub fn union_with(&mut self, other: impl AsRef<[u64]>) {
        self.update(
            #[inline(always)]
            |rb| {
                let mut iter = other.as_ref().iter();
                for (dst, src) in rb.iter_mut().zip(&mut iter) {
                    *dst |= *src;
                }

                let rem = {
                    let mut riter = iter.as_slice();
                    while let [rest @ .., 0] = riter {
                        riter = rest;
                    }
                    riter
                };
                if !rem.is_empty() {
                    rb.extend_from_slice(rem);
                }
            },
        );
    }

    /// Creates a new set that is the union of this set and another set.
    ///
    /// The union contains elements present in either this set or the other
    /// set.
    ///
    /// Time complexity: O(n) where n is the max number of bytes in either
    /// set.
    #[must_use]
    pub fn union(&self, other: impl AsRef<[u64]>) -> Self {
        let mut result = self.clone();
        result.union_with(other);
        result
    }

    /// Performs a bitwise AND operation with another bitmap.
    ///
    /// This sets each bit in `self` to `self[i] & other[i]`. The result
    /// is truncated to the length of the shorter bitmap. Trailing zeros
    /// are removed.
    ///
    /// # Examples
    ///
    /// ```
    /// # use smol_bitmap::SmolBitmap;
    /// let mut a = SmolBitmap::new();
    /// let mut b = SmolBitmap::new();
    ///
    /// a.set(10, true);
    /// a.set(20, true);
    /// b.set(10, true);
    ///
    /// a.intersection_with(&b);
    /// assert!(a.get(10));
    /// assert!(!a.get(20));
    /// ```
    pub fn intersection_with(&mut self, other: impl AsRef<[u64]>) {
        self.update(
            #[inline(always)]
            |rb| {
                let other_slice = other.as_ref();
                let len = rb.len().min(other_slice.len());

                // Process intersection
                for i in 0..len {
                    rb[i] &= other_slice[i];
                }

                // Clear any remaining words beyond other's length
                for i in len..rb.len() {
                    rb[i] = 0;
                }

                // Find last non-zero from the end (more cache-friendly)
                let n = rb.iter().rposition(|&w| w != 0).map_or(0, |i| i + 1);
                rb.truncate(n);
            },
        );
    }

    /// Creates a new set that is the intersection of this set and another
    /// set.
    ///
    /// The intersection contains only elements present in both sets.
    ///
    /// Time complexity: O(n) where n is the min number of bytes in either
    /// set.
    #[must_use]
    pub fn intersection(&self, other: impl AsRef<[u64]>) -> Self {
        let mut result = self.clone();
        result.intersection_with(other);
        result
    }

    /// Creates a new set that is the difference of this set and another
    /// set.
    ///
    /// The difference contains elements present in this set but not in the
    /// other set.
    ///
    /// Time complexity: O(n) where n is the number of bytes in self.
    #[must_use]
    pub fn difference(&self, other: impl AsRef<[u64]>) -> Self {
        let mut result = self.clone();
        result.difference_with(other);
        result
    }

    /// Updates this set to be the difference of itself and another set.
    ///
    /// Time complexity: O(n) where n is the min number of bytes in either
    /// set.
    pub fn difference_with(&mut self, other: impl AsRef<[u64]>) {
        self.update(
            #[inline(always)]
            |rb| {
                let mut n = 0;
                for (i, (dst, &src)) in rb.iter_mut().zip(other.as_ref()).enumerate() {
                    let r = *dst & !src;
                    *dst = r;
                    if r != 0 {
                        n = i + 1;
                    }
                }
                // Bytes beyond other's length remain unchanged
                // as they represent ordinals not in other

                rb.truncate(n);
            },
        );
    }

    /// Creates a new set that is the symmetric difference of this set and
    /// another set.
    ///
    /// The symmetric difference contains elements present in either this
    /// set or the other set, but not in both.
    ///
    /// Time complexity: O(n) where n is the max number of words in either
    /// set.
    #[must_use]
    pub fn symmetric_difference(&self, other: impl AsRef<[u64]>) -> Self {
        let mut result = self.clone();
        result.symmetric_difference_with(other);
        result
    }

    /// Updates this set to be the symmetric difference of itself and
    /// another set.
    ///
    /// Time complexity: O(n) where n is the max number of words in either
    /// set.
    pub fn symmetric_difference_with(&mut self, other: impl AsRef<[u64]>) {
        self.update(
            #[inline(always)]
            |rb| {
                let mut iter = other.as_ref().iter();
                for (dst, src) in rb.iter_mut().zip(&mut iter) {
                    *dst ^= *src;
                }

                let rem = {
                    let mut riter = iter.as_slice();
                    while let [rest @ .., 0] = riter {
                        riter = rest;
                    }
                    riter
                };
                if !rem.is_empty() {
                    rb.extend_from_slice(rem);
                }
            },
        );
    }

    /// Checks if this set is a subset of another set.
    ///
    /// A set is a subset if all its elements are contained in the other
    /// set.
    ///
    /// Time complexity: O(n) where n is the number of words in self.
    #[must_use]
    pub fn is_subset(&self, other: impl AsRef<[u64]>) -> bool {
        let other_slice = other.as_ref();
        let self_slice = self.as_slice();

        // For each word in self, check if (self & !other) == 0
        // If any word has bits set in self but not in other, it's not a subset
        for (i, &word) in self_slice.iter().enumerate() {
            if word == 0 {
                continue; // No bits set in this word, nothing to check
            }

            if i >= other_slice.len() {
                return false; // Self has bits set beyond other's length
            }

            if word & !other_slice[i] != 0 {
                return false; // Self has bits set that other doesn't
            }
        }

        true
    }

    /// Checks if this set is a superset of another set.
    ///
    /// A set is a superset if it contains all elements of the other set.
    ///
    /// Time complexity: O(n) where n is the number of words in other.
    #[must_use]
    pub fn is_superset(&self, other: impl AsRef<[u64]>) -> bool {
        let other_slice = other.as_ref();
        let self_slice = self.as_slice();

        // For each word in other, check if (other & !self) == 0
        // If any word has bits set in other but not in self, it's not a superset
        for (i, &word) in other_slice.iter().enumerate() {
            if word == 0 {
                continue; // No bits set in this word, nothing to check
            }

            if i >= self_slice.len() {
                return false; // Other has bits set beyond self's length
            }

            if word & !self_slice[i] != 0 {
                return false; // Other has bits set that self doesn't
            }
        }

        true
    }

    /// Checks if this set is disjoint from another set.
    ///
    /// Two sets are disjoint if they have no elements in common.
    ///
    /// Time complexity: O(n) where n is the min number of words in either
    /// set.
    #[must_use]
    pub fn is_disjoint(&self, other: impl AsRef<[u64]>) -> bool {
        let other_slice = other.as_ref();
        let self_slice = self.as_slice();
        let len = self_slice.len().min(other_slice.len());

        // Check if intersection is empty by verifying (self & other) == 0
        for i in 0..len {
            if self_slice[i] & other_slice[i] != 0 {
                return false; // Intersection not empty
            }
        }

        true
    }

    /// Returns `true` if all bits up to the maximum set bit are set.
    ///
    /// Returns `true` for an empty bitmap.
    ///
    /// # Examples
    ///
    /// ```
    /// use smol_bitmap::SmolBitmap;
    ///
    /// let mut bitmap = SmolBitmap::new();
    /// assert!(bitmap.all()); // Empty bitmap
    ///
    /// bitmap.set(0, true);
    /// bitmap.set(1, true);
    /// bitmap.set(2, true);
    /// assert!(bitmap.all()); // All bits 0-2 are set
    ///
    /// bitmap.set(4, true);
    /// assert!(!bitmap.all()); // Bit 3 is not set
    /// ```
    #[must_use]
    pub fn all(&self) -> bool {
        if let Some(max_bit) = self.last() {
            let (last_wi, last_bi) = bitpos(max_bit);
            let slice = self.as_slice();

            // Check complete words
            for i in 0..last_wi {
                if i >= slice.len() || slice[i] != !0 {
                    return false;
                }
            }

            // Check partial last word
            if last_wi < slice.len() {
                let mask = (1u64 << (last_bi + 1)) - 1;
                slice[last_wi] & mask == mask
            } else {
                false
            }
        } else {
            // Empty bitmap
            true
        }
    }

    /// Returns `true` if no bits are set.
    ///
    /// This is equivalent to `self.is_empty()`.
    ///
    /// # Examples
    ///
    /// ```
    /// use smol_bitmap::SmolBitmap;
    ///
    /// let mut bitmap = SmolBitmap::new();
    /// assert!(bitmap.none());
    ///
    /// bitmap.set(42, true);
    /// assert!(!bitmap.none());
    /// ```
    #[inline]
    #[must_use]
    pub fn none(&self) -> bool {
        self.is_empty()
    }
}
