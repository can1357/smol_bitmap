//! Trait implementations for `SmolBitmap`.

use crate::{
    SmolBitmap,
    storage::{BitArray, SmolBitmapBuilder},
};
use alloc::vec::Vec;
use core::{
    borrow::Borrow,
    cmp::Ordering,
    convert::TryFrom,
    fmt,
    hash::{Hash, Hasher},
    mem,
    ops::{BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Not},
    str::FromStr,
};

/// Errors that can occur when parsing a binary string into a [`SmolBitmap`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ParseBitmapError {
    /// Invalid character found in the binary string.
    InvalidChar {
        /// The invalid character found
        ch: char,
        /// The position of the invalid character
        pos: usize,
    },

    /// Empty string provided.
    Empty,
}

impl fmt::Display for ParseBitmapError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidChar { ch: char, pos } => {
                write!(
                    f,
                    "invalid character '{char}' at position {pos} in binary string"
                )
            }
            Self::Empty => write!(f, "cannot parse bitmap from empty string"),
        }
    }
}

#[cfg(feature = "std")]
impl std::error::Error for ParseBitmapError {}

/// Error type for converting `SmolBitmap` to primitive integers.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TryFromBitmapError {
    /// The bitmap has too many bits to fit in the target type.
    TooManyBits {
        /// Maximum number of bits the target type can hold
        max_bits: usize,
        /// Number of bits needed
        actual_bits: usize,
    },
}

impl fmt::Display for TryFromBitmapError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::TooManyBits {
                max_bits,
                actual_bits,
            } => {
                write!(
                    f,
                    "bitmap has {actual_bits} bits but target type can only hold {max_bits} bits"
                )
            }
        }
    }
}

#[cfg(feature = "std")]
impl std::error::Error for TryFromBitmapError {}

impl Default for SmolBitmap {
    fn default() -> Self {
        Self::new()
    }
}

impl Clone for SmolBitmap {
    fn clone(&self) -> Self {
        Self::from(self.as_slice_rtrim())
    }
}

impl From<SmolBitmap> for Vec<u64> {
    fn from(bitmap: SmolBitmap) -> Self {
        bitmap.into_inner().into_vec()
    }
}

impl From<Vec<u64>> for SmolBitmap {
    fn from(words: Vec<u64>) -> Self {
        Self {
            array: BitArray::from(words).pack(),
        }
    }
}

impl From<&[u64]> for SmolBitmap {
    fn from(slice: &[u64]) -> Self {
        Self {
            array: BitArray::from(slice).pack(),
        }
    }
}

impl<const N: usize> From<&[u64; N]> for SmolBitmap {
    fn from(slice: &[u64; N]) -> Self {
        Self {
            array: BitArray::from(slice).pack(),
        }
    }
}

impl Borrow<[u64]> for SmolBitmap {
    fn borrow(&self) -> &[u64] {
        self.as_slice()
    }
}

impl AsRef<[u64]> for SmolBitmap {
    fn as_ref(&self) -> &[u64] {
        self.as_slice()
    }
}

impl fmt::Display for SmolBitmap {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Binary::fmt(self, f)
    }
}

impl fmt::Binary for SmolBitmap {
    /// Formats the bitmap as a binary string representation.
    ///
    /// The binary representation shows bits from least significant (rightmost)
    /// to most significant (leftmost), with the `0b` prefix. Trailing zeros
    /// are omitted for compact representation.
    ///
    /// # Examples
    ///
    /// ```
    /// use smol_bitmap::SmolBitmap;
    /// let mut bitmap = SmolBitmap::new();
    /// bitmap.insert(0);
    /// bitmap.insert(2);
    /// bitmap.insert(65);
    ///
    /// // Shows compact binary representation
    /// println!("{:#b}", bitmap); // 0b10000000000000000000000000000000000000000000000000000000000000000101
    /// ```
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let slice = self.as_slice_rtrim();

        let [rem @ .., hi] = slice else {
            return f.write_str(if f.alternate() { "0b0" } else { "0" });
        };

        if f.alternate() {
            write!(f, "0b{hi:b}")?;
        } else {
            write!(f, "{hi:b}")?;
        }
        for &word in rem.iter().rev() {
            write!(f, "{word:064b}")?;
        }
        Ok(())
    }
}

impl FromStr for SmolBitmap {
    type Err = ParseBitmapError;

    /// Parses a binary string representation into a [`SmolBitmap`].
    ///
    /// The input string can optionally start with `0b` and contain only '0' and
    /// '1' characters. The string is interpreted with the least significant bit
    /// on the right.
    ///
    /// # Errors
    ///
    /// Returns a [`ParseBitmapError`] if the string contains invalid characters
    /// or cannot be parsed as binary.
    ///
    /// # Examples
    ///
    /// ```
    /// use core::str::FromStr;
    /// use smol_bitmap::SmolBitmap;
    ///
    /// let bitmap = SmolBitmap::from_str("0b101")?;
    /// assert!(bitmap.get(0)); // bit 0 set
    /// assert!(!bitmap.get(1)); // bit 1 unset
    /// assert!(bitmap.get(2)); // bit 2 set
    ///
    /// # Ok::<(), smol_bitmap::ParseBitmapError>(())
    /// ```
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let s = s.strip_prefix("0b").unwrap_or(s).as_bytes();
        if s.is_empty() {
            return Err(ParseBitmapError::Empty);
        }

        // Process bits in chunks of 64 from right to left
        let mut bm = SmolBitmapBuilder::with_capacity(s.len().div_ceil(64));
        let mut twidth = 0;
        let mut tvalue = 0;
        for (pos, &v) in s.iter().enumerate().rev() {
            let bit: u64 = match v {
                b'1' => 1,
                b'0' => 0,
                b'_' => continue,
                _ => {
                    return Err(ParseBitmapError::InvalidChar { ch: v as char, pos });
                }
            };
            tvalue |= bit << twidth;
            twidth += 1;
            if twidth == 64 {
                bm.push(mem::replace(&mut tvalue, 0));
                twidth = 0;
            }
        }
        if twidth != 0 && tvalue != 0 {
            bm.push(tvalue);
        }
        Ok(bm.into())
    }
}

impl fmt::Debug for SmolBitmap {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut w = f.debug_set();
        for bit in self {
            w.entry(&bit);
        }
        w.finish()
    }
}

impl PartialEq for SmolBitmap {
    fn eq(&self, other: &Self) -> bool {
        self.eq_rtrim(other.as_slice())
    }
}

impl Eq for SmolBitmap {}

impl PartialOrd for SmolBitmap {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for SmolBitmap {
    fn cmp(&self, other: &Self) -> Ordering {
        self.cmp_rtrim(other.as_slice())
    }
}

impl Hash for SmolBitmap {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.as_slice_rtrim().hash(state);
    }
}

// Cleanup on drop
impl Drop for SmolBitmap {
    fn drop(&mut self) {
        drop(self.take_inner());
    }
}

// ============================================================================
// Bitwise Operator Implementations
// ============================================================================

impl BitAnd for SmolBitmap {
    type Output = Self;

    /// Performs bitwise AND operation between two bitmaps.
    ///
    /// # Examples
    ///
    /// ```
    /// use smol_bitmap::SmolBitmap;
    ///
    /// let mut a = SmolBitmap::new();
    /// a.insert(0);
    /// a.insert(1);
    ///
    /// let mut b = SmolBitmap::new();
    /// b.insert(1);
    /// b.insert(2);
    ///
    /// let c = a & b;
    /// assert!(c.get(1)); // Only bit 1 is set in both
    /// assert!(!c.get(0));
    /// assert!(!c.get(2));
    /// ```
    #[inline]
    fn bitand(self, rhs: Self) -> Self::Output {
        self.intersection(&rhs)
    }
}

impl BitAnd for &SmolBitmap {
    type Output = SmolBitmap;

    #[inline]
    fn bitand(self, rhs: Self) -> Self::Output {
        self.intersection(rhs)
    }
}

impl BitAndAssign for SmolBitmap {
    /// Performs in-place bitwise AND operation.
    ///
    /// # Examples
    ///
    /// ```
    /// use smol_bitmap::SmolBitmap;
    ///
    /// let mut a = SmolBitmap::new();
    /// a.insert(0);
    /// a.insert(1);
    ///
    /// let mut b = SmolBitmap::new();
    /// b.insert(1);
    /// b.insert(2);
    ///
    /// a &= b;
    /// assert!(a.get(1)); // Only bit 1 is set in both
    /// assert!(!a.get(0));
    /// ```
    #[inline]
    fn bitand_assign(&mut self, rhs: Self) {
        self.intersection_with(&rhs);
    }
}

impl BitAndAssign<&Self> for SmolBitmap {
    #[inline]
    fn bitand_assign(&mut self, rhs: &Self) {
        self.intersection_with(rhs);
    }
}

impl BitOr for SmolBitmap {
    type Output = Self;

    /// Performs bitwise OR operation between two bitmaps.
    ///
    /// # Examples
    ///
    /// ```
    /// use smol_bitmap::SmolBitmap;
    ///
    /// let mut a = SmolBitmap::new();
    /// a.insert(0);
    /// a.insert(1);
    ///
    /// let mut b = SmolBitmap::new();
    /// b.insert(1);
    /// b.insert(2);
    ///
    /// let c = a | b;
    /// assert!(c.get(0));
    /// assert!(c.get(1));
    /// assert!(c.get(2));
    /// ```
    #[inline]
    fn bitor(self, rhs: Self) -> Self::Output {
        self.union(&rhs)
    }
}

impl BitOr for &SmolBitmap {
    type Output = SmolBitmap;

    #[inline]
    fn bitor(self, rhs: Self) -> Self::Output {
        self.union(rhs)
    }
}

impl BitOrAssign for SmolBitmap {
    /// Performs in-place bitwise OR operation.
    ///
    /// # Examples
    ///
    /// ```
    /// use smol_bitmap::SmolBitmap;
    ///
    /// let mut a = SmolBitmap::new();
    /// a.insert(0);
    ///
    /// let mut b = SmolBitmap::new();
    /// b.insert(1);
    ///
    /// a |= b;
    /// assert!(a.get(0));
    /// assert!(a.get(1));
    /// ```
    #[inline]
    fn bitor_assign(&mut self, rhs: Self) {
        self.union_with(&rhs);
    }
}

impl BitOrAssign<&Self> for SmolBitmap {
    #[inline]
    fn bitor_assign(&mut self, rhs: &Self) {
        self.union_with(rhs);
    }
}

impl BitXor for SmolBitmap {
    type Output = Self;

    /// Performs bitwise XOR operation between two bitmaps.
    ///
    /// # Examples
    ///
    /// ```
    /// use smol_bitmap::SmolBitmap;
    ///
    /// let mut a = SmolBitmap::new();
    /// a.insert(0);
    /// a.insert(1);
    ///
    /// let mut b = SmolBitmap::new();
    /// b.insert(1);
    /// b.insert(2);
    ///
    /// let c = a ^ b;
    /// assert!(c.get(0)); // Only in a
    /// assert!(!c.get(1)); // In both, so not in XOR
    /// assert!(c.get(2)); // Only in b
    /// ```
    #[inline]
    fn bitxor(self, rhs: Self) -> Self::Output {
        self.symmetric_difference(&rhs)
    }
}

impl BitXor for &SmolBitmap {
    type Output = SmolBitmap;

    #[inline]
    fn bitxor(self, rhs: Self) -> Self::Output {
        self.symmetric_difference(rhs)
    }
}

impl BitXorAssign for SmolBitmap {
    /// Performs in-place bitwise XOR operation.
    ///
    /// # Examples
    ///
    /// ```
    /// use smol_bitmap::SmolBitmap;
    ///
    /// let mut a = SmolBitmap::new();
    /// a.insert(0);
    /// a.insert(1);
    ///
    /// let mut b = SmolBitmap::new();
    /// b.insert(1);
    /// b.insert(2);
    ///
    /// a ^= b;
    /// assert!(a.get(0)); // Only in original a
    /// assert!(!a.get(1)); // In both, so removed
    /// assert!(a.get(2)); // Only in b
    /// ```
    #[inline]
    fn bitxor_assign(&mut self, rhs: Self) {
        self.symmetric_difference_with(&rhs);
    }
}

impl BitXorAssign<&Self> for SmolBitmap {
    #[inline]
    fn bitxor_assign(&mut self, rhs: &Self) {
        self.symmetric_difference_with(rhs);
    }
}

impl Not for SmolBitmap {
    type Output = Self;

    /// Returns the bitwise complement of the bitmap up to its capacity.
    ///
    /// # Examples
    ///
    /// ```
    /// use smol_bitmap::SmolBitmap;
    ///
    /// let mut a = SmolBitmap::new();
    /// a.insert(0);
    /// a.insert(2);
    ///
    /// let b = !a.clone();
    /// assert!(!b.get(0));
    /// assert!(b.get(1));
    /// assert!(!b.get(2));
    /// ```
    #[inline]
    fn not(mut self) -> Self::Output {
        self.complement_range(0, self.last().map_or(0, |max_bit| max_bit + 1));
        self
    }
}

impl Not for &SmolBitmap {
    type Output = SmolBitmap;

    #[inline]
    fn not(self) -> Self::Output {
        self.clone().not()
    }
}

// ============================================================================
// From Primitive Integer Implementations
// ============================================================================

impl From<u8> for SmolBitmap {
    /// Creates a bitmap from an 8-bit unsigned integer.
    ///
    /// # Examples
    ///
    /// ```
    /// use smol_bitmap::SmolBitmap;
    ///
    /// let bitmap = SmolBitmap::from(0b10101010u8);
    /// assert!(!bitmap.get(0));
    /// assert!(bitmap.get(1));
    /// assert!(!bitmap.get(2));
    /// assert!(bitmap.get(3));
    /// ```
    fn from(value: u8) -> Self {
        Self::from(u64::from(value))
    }
}

impl From<u16> for SmolBitmap {
    /// Creates a bitmap from a 16-bit unsigned integer.
    ///
    /// # Examples
    ///
    /// ```
    /// use smol_bitmap::SmolBitmap;
    ///
    /// let bitmap = SmolBitmap::from(0x1234u16);
    /// // Bits are set according to the binary representation
    /// ```
    fn from(value: u16) -> Self {
        Self::from(u64::from(value))
    }
}

impl From<u32> for SmolBitmap {
    /// Creates a bitmap from a 32-bit unsigned integer.
    ///
    /// # Examples
    ///
    /// ```
    /// use smol_bitmap::SmolBitmap;
    ///
    /// let bitmap = SmolBitmap::from(0x12345678u32);
    /// // Bits are set according to the binary representation
    /// ```
    fn from(value: u32) -> Self {
        Self::from(u64::from(value))
    }
}

impl From<u64> for SmolBitmap {
    /// Creates a bitmap from a 64-bit unsigned integer.
    ///
    /// # Examples
    ///
    /// ```
    /// use smol_bitmap::SmolBitmap;
    ///
    /// let bitmap = SmolBitmap::from(0b1010u64);
    /// assert!(!bitmap.get(0));
    /// assert!(bitmap.get(1));
    /// assert!(!bitmap.get(2));
    /// assert!(bitmap.get(3));
    /// ```
    fn from(value: u64) -> Self {
        if value == 0 {
            Self::new()
        } else {
            Self::from(&[value] as &[u64])
        }
    }
}

impl From<u128> for SmolBitmap {
    /// Creates a bitmap from a 128-bit unsigned integer.
    ///
    /// # Examples
    ///
    /// ```
    /// use smol_bitmap::SmolBitmap;
    ///
    /// let bitmap = SmolBitmap::from(0x123456789ABCDEFu128);
    /// // Bits are set according to the binary representation
    /// ```
    fn from(value: u128) -> Self {
        if value == 0 {
            Self::new()
        } else {
            let low = value as u64;
            let high = (value >> 64) as u64;
            if high == 0 {
                Self::from(&[low] as &[u64])
            } else {
                Self::from(&[low, high] as &[u64])
            }
        }
    }
}

// ============================================================================
// TryFrom SmolBitmap for Primitive Integers
// ============================================================================

impl TryFrom<&SmolBitmap> for u8 {
    type Error = TryFromBitmapError;

    /// Attempts to convert a bitmap to an 8-bit unsigned integer.
    ///
    /// # Errors
    ///
    /// Returns an error if the bitmap has bits set beyond position 7.
    ///
    /// # Examples
    ///
    /// ```
    /// use core::convert::TryFrom;
    /// use smol_bitmap::SmolBitmap;
    ///
    /// let mut bitmap = SmolBitmap::new();
    /// bitmap.insert(1);
    /// bitmap.insert(3);
    ///
    /// let value = u8::try_from(&bitmap).unwrap();
    /// assert_eq!(value, 0b00001010);
    /// ```
    fn try_from(bitmap: &SmolBitmap) -> Result<Self, Self::Error> {
        if let Some(last) = bitmap.last()
            && last >= 8
        {
            return Err(TryFromBitmapError::TooManyBits {
                max_bits: 8,
                actual_bits: last + 1,
            });
        }

        Ok(bitmap.get_range(0, 8) as Self)
    }
}

impl TryFrom<&SmolBitmap> for u16 {
    type Error = TryFromBitmapError;

    /// Attempts to convert a bitmap to a 16-bit unsigned integer.
    ///
    /// # Errors
    ///
    /// Returns an error if the bitmap has bits set beyond position 15.
    fn try_from(bitmap: &SmolBitmap) -> Result<Self, Self::Error> {
        if let Some(last) = bitmap.last()
            && last >= 16
        {
            return Err(TryFromBitmapError::TooManyBits {
                max_bits: 16,
                actual_bits: last + 1,
            });
        }

        Ok(bitmap.get_range(0, 16) as Self)
    }
}

impl TryFrom<&SmolBitmap> for u32 {
    type Error = TryFromBitmapError;

    /// Attempts to convert a bitmap to a 32-bit unsigned integer.
    ///
    /// # Errors
    ///
    /// Returns an error if the bitmap has bits set beyond position 31.
    fn try_from(bitmap: &SmolBitmap) -> Result<Self, Self::Error> {
        if let Some(last) = bitmap.last()
            && last >= 32
        {
            return Err(TryFromBitmapError::TooManyBits {
                max_bits: 32,
                actual_bits: last + 1,
            });
        }

        Ok(bitmap.get_range(0, 32) as Self)
    }
}

impl TryFrom<&SmolBitmap> for u64 {
    type Error = TryFromBitmapError;

    /// Attempts to convert a bitmap to a 64-bit unsigned integer.
    ///
    /// # Errors
    ///
    /// Returns an error if the bitmap has bits set beyond position 63.
    fn try_from(bitmap: &SmolBitmap) -> Result<Self, Self::Error> {
        if let Some(last) = bitmap.last()
            && last >= 64
        {
            return Err(TryFromBitmapError::TooManyBits {
                max_bits: 64,
                actual_bits: last + 1,
            });
        }

        Ok(bitmap.get_range(0, 64))
    }
}

impl TryFrom<&SmolBitmap> for u128 {
    type Error = TryFromBitmapError;

    /// Attempts to convert a bitmap to a 128-bit unsigned integer.
    ///
    /// # Errors
    ///
    /// Returns an error if the bitmap has bits set beyond position 127.
    fn try_from(bitmap: &SmolBitmap) -> Result<Self, Self::Error> {
        if let Some(last) = bitmap.last()
            && last >= 128
        {
            return Err(TryFromBitmapError::TooManyBits {
                max_bits: 128,
                actual_bits: last + 1,
            });
        }

        let low = Self::from(bitmap.get_range(0, 64));
        let high = Self::from(bitmap.get_range(64, 128));
        Ok(low | (high << 64))
    }
}

// ============================================================================
// Display Format Implementations
// ============================================================================

impl fmt::LowerHex for SmolBitmap {
    /// Formats the bitmap as a lowercase hexadecimal string.
    ///
    /// # Examples
    ///
    /// ```
    /// use smol_bitmap::SmolBitmap;
    ///
    /// let bitmap = SmolBitmap::from(0xDEADBEEFu32);
    /// assert_eq!(format!("{:x}", bitmap), "deadbeef");
    /// assert_eq!(format!("{:#x}", bitmap), "0xdeadbeef");
    /// ```
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let slice = self.as_slice_rtrim();

        if slice.is_empty() {
            return if f.alternate() {
                f.write_str("0x0")
            } else {
                f.write_str("0")
            };
        }

        if f.alternate() {
            f.write_str("0x")?;
        }

        // Write words in reverse order for natural reading
        let mut started = false;
        for &word in slice.iter().rev() {
            if started || word != 0 {
                if started {
                    write!(f, "{word:016x}")?;
                } else {
                    write!(f, "{word:x}")?;
                    started = true;
                }
            }
        }

        if !started {
            f.write_str("0")?;
        }

        Ok(())
    }
}

impl fmt::UpperHex for SmolBitmap {
    /// Formats the bitmap as an uppercase hexadecimal string.
    ///
    /// # Examples
    ///
    /// ```
    /// use smol_bitmap::SmolBitmap;
    ///
    /// let bitmap = SmolBitmap::from(0xDEADBEEFu32);
    /// assert_eq!(format!("{:X}", bitmap), "DEADBEEF");
    /// assert_eq!(format!("{:#X}", bitmap), "0xDEADBEEF");
    /// ```
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let slice = self.as_slice_rtrim();

        if slice.is_empty() {
            return if f.alternate() {
                f.write_str("0x0")
            } else {
                f.write_str("0")
            };
        }

        if f.alternate() {
            f.write_str("0x")?;
        }

        // Write words in reverse order for natural reading
        let mut started = false;
        for &word in slice.iter().rev() {
            if started || word != 0 {
                if started {
                    write!(f, "{word:016X}")?;
                } else {
                    write!(f, "{word:X}")?;
                    started = true;
                }
            }
        }

        if !started {
            f.write_str("0")?;
        }

        Ok(())
    }
}

impl fmt::Octal for SmolBitmap {
    /// Formats the bitmap as an octal string.
    ///
    /// # Examples
    ///
    /// ```
    /// use smol_bitmap::SmolBitmap;
    ///
    /// let bitmap = SmolBitmap::from(0b111000u8);
    /// assert_eq!(format!("{:o}", bitmap), "70");
    /// assert_eq!(format!("{:#o}", bitmap), "0o70");
    /// ```
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let slice = self.as_slice_rtrim();

        if slice.is_empty() {
            return if f.alternate() {
                f.write_str("0o0")
            } else {
                f.write_str("0")
            };
        }

        if f.alternate() {
            f.write_str("0o")?;
        }

        // Convert to octal - this is a bit more complex as octal doesn't align with
        // 64-bit words For simplicity, convert to bytes first
        let bytes = self.to_le_bytes();
        if bytes.is_empty() {
            return f.write_str("0");
        }

        // Process bytes in groups of 3 bits
        let mut result = Vec::new();
        let mut accumulator = 0u32;
        let mut bits = 0;

        for &byte in bytes.as_ref() {
            accumulator |= u32::from(byte) << bits;
            bits += 8;

            while bits >= 3 {
                result.push((accumulator & 0x7) as u8);
                accumulator >>= 3;
                bits -= 3;
            }
        }

        if bits > 0 {
            result.push(accumulator as u8);
        }

        // Remove leading zeros and reverse
        while result.last() == Some(&0) && result.len() > 1 {
            result.pop();
        }

        for &digit in result.iter().rev() {
            write!(f, "{digit}")?;
        }

        Ok(())
    }
}
