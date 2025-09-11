//! Iterator implementations for `SmolBitmap`.

use core::{
    borrow::Borrow,
    iter::{FromIterator, FusedIterator},
};

use crate::{SmolBitmap, macros::bitpos};

/// An iterator over the indices of set bits in a [`SmolBitmap`].
///
/// This struct is created by the [`iter`](SmolBitmap::iter) method on
/// [`SmolBitmap`]. It yields the indices of all set bits in ascending order.
pub type Iter<'a> = BitIter<&'a [u64]>;

/// An owning iterator over the indices of set bits in a [`SmolBitmap`].
///
/// This struct is created by the [`IntoIterator`] implementation for
/// [`SmolBitmap`]. It consumes the bitmap and yields the indices of all set
/// bits in ascending order.
pub type IntoIter = BitIter<SmolBitmap>;

/// An iterator that selects elements from another iterator based on set bits in
/// a bitmap.
///
/// This iterator yields elements from the underlying iterator only at positions
/// corresponding to set bits in the bitmap. It's created by the
/// [`select`](SmolBitmap::select) method on [`SmolBitmap`].
///
/// # Examples
///
/// ```
/// use smol_bitmap::SmolBitmap;
/// let mut bitmap = SmolBitmap::new();
/// bitmap.insert(1);
/// bitmap.insert(3);
///
/// let numbers = vec![10, 20, 30, 40, 50];
/// let selected: Vec<_> = bitmap.select(numbers).collect();
/// assert_eq!(selected, vec![20, 40]);
/// ```
pub struct SelectIter<'a, I> {
    words: &'a [u64],
    next: usize,
    it: I,
}

impl<'a, I: Iterator> SelectIter<'a, I> {
    /// Creates a new `SelectIter` that filters the given iterator based on set
    /// bits in the bitmap.
    ///
    /// # Arguments
    ///
    /// * `bitmap` - The bitmap whose set bits determine which elements to
    ///   select
    /// * `it` - The iterator to filter based on the bitmap
    ///
    /// # Examples
    ///
    /// ```
    /// use smol_bitmap::{SelectIter, SmolBitmap};
    /// let mut bitmap = SmolBitmap::new();
    /// bitmap.insert(0);
    /// bitmap.insert(2);
    ///
    /// let items = vec![1, 2, 3, 4, 5];
    /// let selected: Vec<_> = SelectIter::new(&bitmap, items).collect();
    /// assert_eq!(selected, vec![1, 3]);
    /// ```
    pub fn new(bitmap: &'a SmolBitmap, it: impl IntoIterator<IntoIter = I>) -> Self {
        Self {
            words: bitmap.as_slice_rtrim(),
            next: 0,
            it: it.into_iter(),
        }
    }

    fn next_pos(&mut self) -> Option<usize> {
        let (mut wi, mut bi) = bitpos!(self.next);
        while let Some(word) = self.words.get(wi) {
            let word = *word >> bi;
            if word == 0 {
                wi += 1;
                bi = 0;
                continue;
            }
            let pos = (word.trailing_zeros() as usize) + bi + wi * 64;
            self.next = pos + 1;
            return Some(pos);
        }

        None
    }

    fn popcnt_rem(&self) -> usize {
        let (wi, bi) = bitpos!(self.next);
        self.words
            .iter()
            .skip(wi)
            .copied()
            .enumerate()
            .map(|(i, mut w)| {
                if i == 0 {
                    w >>= bi;
                }
                w.count_ones() as usize
            })
            .sum()
    }
}

impl<I: Iterator> Iterator for SelectIter<'_, I> {
    type Item = I::Item;

    fn next(&mut self) -> Option<Self::Item> {
        let base = self.next;
        if let Some(pos) = self.next_pos()
            && let Some(item) = self.it.nth(pos - base)
        {
            return Some(item);
        }

        self.words = &[];
        None
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let (omin, omax) = self.it.size_hint();
        let limit = self.popcnt_rem();
        (omin.min(limit), omax.map(|omax| omax.min(limit)))
    }
}

impl<I: ExactSizeIterator> ExactSizeIterator for SelectIter<'_, I> {
    fn len(&self) -> usize {
        self.popcnt_rem().min(self.it.len())
    }
}

impl<I: FusedIterator> FusedIterator for SelectIter<'_, I> {}

/// An iterator over the indices of set bits in a bitmap.
///
/// This iterator is double-ended, allowing iteration from both the beginning
/// and end of the bitmap. It efficiently skips over words that contain no set
/// bits.
///
/// The generic parameter `S` allows this iterator to work with both borrowed
/// and owned bitmap data.
///
/// # Examples
///
/// ```
/// use smol_bitmap::SmolBitmap;
/// let mut bitmap = SmolBitmap::new();
/// bitmap.insert(5);
/// bitmap.insert(10);
/// bitmap.insert(15);
///
/// // Forward iteration
/// let indices: Vec<_> = bitmap.iter().collect();
/// assert_eq!(indices, vec![5, 10, 15]);
///
/// // Reverse iteration
/// let rev_indices: Vec<_> = bitmap.iter().rev().collect();
/// assert_eq!(rev_indices, vec![15, 10, 5]);
/// ```
#[derive(Clone)]
pub struct BitIter<S: Borrow<[u64]>> {
    pub(crate) words: S,
    pub(crate) pos: usize,  // current bit position (forward)
    pub(crate) rpos: usize, // current bit position (reverse)
}

impl<S: Borrow<[u64]>> Iterator for BitIter<S> {
    type Item = usize;

    fn next(&mut self) -> Option<Self::Item> {
        let slice = self.words.borrow();

        while self.pos < self.rpos {
            let (mut wi, bi) = bitpos!(self.pos);
            if wi >= slice.len() {
                return None;
            }

            // Skip consecutive zero words efficiently
            let word = slice[wi] >> bi;
            if word == 0 {
                // Skip to next word
                wi += 1;

                // Skip multiple zero words at once
                while wi < slice.len() && slice[wi] == 0 {
                    wi += 1;
                }

                self.pos = wi * 64;
                continue;
            }

            let offset = word.trailing_zeros();
            let result = self.pos + offset as usize;
            self.pos = result + 1;

            if result >= self.rpos {
                return None;
            }

            return Some(result);
        }

        None
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let n = self.len();
        (n, Some(n))
    }
}

impl<S: Borrow<[u64]>> ExactSizeIterator for BitIter<S> {
    fn len(&self) -> usize {
        if self.pos >= self.rpos {
            return 0;
        }

        let slice = self.words.borrow();
        let (wmin, bmin) = bitpos!(self.pos);
        let (wmax, bmax) = bitpos!(self.rpos);

        let mut count = 0;

        if wmin == wmax {
            // All bits are in the same word
            if wmin < slice.len() {
                let word = slice[wmin];
                // Create mask for bits between bmin and bmax (exclusive)
                let mask = if bmax >= 64 {
                    !((1u64 << bmin) - 1)
                } else {
                    ((1u64 << bmax) - 1) & !((1u64 << bmin) - 1)
                };
                count = (word & mask).count_ones() as usize;
            }
        } else {
            // Count bits in the first word (from bmin to end)
            if wmin < slice.len() {
                let mask = !((1u64 << bmin) - 1);
                count += (slice[wmin] & mask).count_ones() as usize;
            }

            // Count bits in middle words (all bits)
            count += slice
                .iter()
                .take(wmax)
                .skip(wmin + 1)
                .map(|&item| item.count_ones() as usize)
                .sum::<usize>();

            // Count bits in the last word (from start to bmax)
            if wmax < slice.len() && bmax > 0 {
                let mask = (1u64 << bmax) - 1;
                count += (slice[wmax] & mask).count_ones() as usize;
            }
        }

        count
    }
}

impl<S: Borrow<[u64]>> FusedIterator for BitIter<S> {}

impl<S: Borrow<[u64]>> DoubleEndedIterator for BitIter<S> {
    fn next_back(&mut self) -> Option<Self::Item> {
        let slice = self.words.borrow();

        while self.rpos > self.pos {
            self.rpos -= 1;
            let (wi, bi) = bitpos!(self.rpos);

            if wi >= slice.len() {
                self.rpos = slice.len() * 64;
                continue;
            }

            let word = slice[wi];
            // Mask to only consider bits up to and including bit_idx
            let mask = if bi == 63 {
                !0u64
            } else {
                (1u64 << (bi + 1)) - 1
            };
            let masked_word = word & mask;

            if masked_word == 0 {
                // No bits set in this range, skip to previous word
                self.rpos = wi * 64;
                continue;
            }

            // Find the highest set bit
            let highest_bit = 63 - masked_word.leading_zeros() as usize;
            let result = wi * 64 + highest_bit;
            self.rpos = result;
            if result < self.pos {
                return None;
            }
            return Some(result);
        }

        None
    }
}

impl<'a> IntoIterator for &'a SmolBitmap {
    type IntoIter = Iter<'a>;
    type Item = usize;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl IntoIterator for SmolBitmap {
    type IntoIter = IntoIter;
    type Item = usize;

    fn into_iter(self) -> Self::IntoIter {
        let cap = self.capacity();
        IntoIter {
            words: self,
            pos: 0,
            rpos: cap,
        }
    }
}

impl FromIterator<usize> for SmolBitmap {
    fn from_iter<I: IntoIterator<Item = usize>>(iter: I) -> Self {
        let mut bitmap = Self::new();
        for bit in iter {
            bitmap.insert(bit);
        }
        bitmap
    }
}

impl Extend<usize> for SmolBitmap {
    fn extend<I: IntoIterator<Item = usize>>(&mut self, iter: I) {
        for bit in iter {
            self.insert(bit);
        }
    }
}
