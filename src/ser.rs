//! Serialization of `SmolBitmap`.

use core::{ptr, slice};

use alloc::{borrow::Cow, vec::Vec};

use crate::{SmolBitmap, storage::SmolBitmapBuilder};

impl SmolBitmap {
    /// Converts the bitmap to a byte slice in native-endian order.
    ///
    /// This method provides a view of the bitmap's internal representation
    /// as a slice of bytes. The byte order is native-endian, meaning it
    /// matches the endianness of the host system.
    ///
    /// # Safety
    ///
    /// The returned slice is valid as long as the bitmap is not modified.
    /// Modifying the bitmap while holding a reference to this slice may
    /// lead to undefined behavior.
    ///
    /// # Examples
    ///
    /// ```
    /// use smol_bitmap::SmolBitmap;
    ///
    /// let mut bitmap = SmolBitmap::new();
    /// bitmap.insert(0);
    /// let bytes = bitmap.to_ne_bytes();
    /// assert_eq!(bytes[0], 0b00000001);
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn to_ne_bytes(&self) -> &[u8] {
        let slice = self.as_slice_rtrim();
        unsafe { slice::from_raw_parts(slice.as_ptr().cast::<u8>(), slice.len() * 8) }
    }

    /// Constructs a bitmap from a byte slice in native-endian order.
    ///
    /// This method reads bytes in native-endian order and constructs a
    /// [`SmolBitmap`] from them. Any remaining bytes that do not form a
    /// complete word are returned as a separate slice.
    ///
    /// # Safety
    ///
    /// The input byte slice must be properly aligned and sized to match
    /// the internal representation of the bitmap. Misalignment or incorrect
    /// sizing may lead to undefined behavior.
    #[inline(always)]
    #[must_use]
    pub fn from_ne_bytes(bytes: &[u8]) -> (Self, &[u8]) {
        let (words, rest) = bytes.as_chunks::<8>();
        let mut builder = SmolBitmapBuilder::with_capacity(words.len());
        unsafe {
            ptr::copy_nonoverlapping(
                words.as_ptr().cast::<u8>(),
                builder.as_mut_ptr().cast::<u8>(),
                words.len() * 8,
            );
            builder.set_len(words.len());
        }
        (builder.into(), rest)
    }
}

#[cfg(target_endian = "little")]
impl SmolBitmap {
    /// Converts the bitmap to little-endian bytes.
    ///
    /// # Examples
    ///
    /// ```
    /// use smol_bitmap::SmolBitmap;
    ///
    /// let mut bitmap = SmolBitmap::new();
    /// bitmap.insert(0);
    /// bitmap.insert(7);
    /// bitmap.insert(8);
    ///
    /// let bytes = bitmap.to_le_bytes();
    /// assert_eq!(bytes[0], 0b10000001); // bits 0 and 7
    /// assert_eq!(bytes[1], 0b00000001); // bit 8
    /// ```
    #[must_use]
    pub const fn to_le_bytes(&self) -> Cow<'_, [u8]> {
        Cow::Borrowed(self.to_ne_bytes())
    }

    /// Constructs a bitmap from little-endian bytes.
    ///
    /// # Examples
    ///
    /// ```
    /// use smol_bitmap::SmolBitmap;
    ///
    /// let bytes = [0b10000001, 0b00000001, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00];
    /// let (bitmap, _rest) = SmolBitmap::from_le_bytes(&bytes);
    ///
    /// assert!(bitmap.get(0)); // bit 0 from byte 0
    /// assert!(bitmap.get(7)); // bit 7 from byte 0
    /// assert!(bitmap.get(8)); // bit 0 from byte 1
    /// ```
    #[must_use]
    pub fn from_le_bytes(bytes: &[u8]) -> (Self, &[u8]) {
        Self::from_ne_bytes(bytes)
    }

    /// Converts the bitmap to big-endian bytes.
    ///
    /// # Examples
    ///
    /// ```
    /// use smol_bitmap::SmolBitmap;
    ///
    /// let mut bitmap = SmolBitmap::new();
    /// bitmap.insert(0);
    /// bitmap.insert(7);
    ///
    /// let bytes = bitmap.to_be_bytes();
    /// // Big-endian representation
    /// ```
    #[must_use]
    pub fn to_be_bytes(&self) -> Cow<'_, [u8]> {
        let slice = self.as_slice_rtrim();
        let mut bytes = Vec::with_capacity(slice.len() * 8);
        bytes.extend(slice.iter().flat_map(|&word| word.to_be_bytes()));
        Cow::Owned(bytes)
    }

    /// Constructs a bitmap from big-endian bytes.
    ///
    /// # Examples
    ///
    /// ```
    /// use smol_bitmap::SmolBitmap;
    ///
    /// let bytes = vec![0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0x00]; // Big-endian representation
    /// let (bitmap, _rest) = SmolBitmap::from_be_bytes(&bytes);
    ///
    /// assert!(bitmap.get(8)); // The high bit of the first byte
    /// ```
    #[must_use]
    pub fn from_be_bytes(bytes: &[u8]) -> (Self, &[u8]) {
        let (words, rest) = bytes.as_chunks::<8>();
        let builder = words
            .iter()
            .map(|&w| u64::from_be_bytes(w))
            .collect::<SmolBitmapBuilder>();
        (builder.into(), rest)
    }
}

#[cfg(target_endian = "big")]
impl SmolBitmap {
    /// Converts the bitmap to big-endian bytes.
    ///
    /// # Examples
    ///
    /// ```
    /// use smol_bitmap::SmolBitmap;
    ///
    /// let mut bitmap = SmolBitmap::new();
    /// bitmap.insert(0);
    /// bitmap.insert(7);
    ///
    /// let bytes = bitmap.to_be_bytes();
    /// // Big-endian representation
    /// ```
    #[must_use]
    pub const fn to_be_bytes(&self) -> Cow<'_, [u8]> {
        Cow::Borrowed(self.to_ne_bytes())
    }

    /// Constructs a bitmap from big-endian bytes.
    ///
    /// # Examples
    ///
    /// ```
    /// use smol_bitmap::SmolBitmap;
    ///
    /// let bytes = vec![0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0x00]; // Big-endian representation
    /// let (bitmap, _rest) = SmolBitmap::from_be_bytes(&bytes);
    ///
    /// assert!(bitmap.get(8)); // The high bit of the first byte
    /// ```
    #[must_use]
    pub fn from_be_bytes(bytes: &[u8]) -> (Self, &[u8]) {
        Self::from_ne_bytes(bytes)
    }

    /// Converts the bitmap to little-endian bytes.
    ///
    /// # Examples
    ///
    /// ```
    /// use smol_bitmap::SmolBitmap;
    ///
    /// let mut bitmap = SmolBitmap::new();
    /// bitmap.insert(0);
    /// bitmap.insert(7);
    /// bitmap.insert(8);
    ///
    /// let bytes = bitmap.to_le_bytes();
    /// assert_eq!(bytes[0], 0b10000001); // bits 0 and 7
    /// assert_eq!(bytes[1], 0b00000001); // bit 8
    /// ```
    #[must_use]
    pub fn to_le_bytes(&self) -> Cow<'_, [u8]> {
        let slice = self.as_slice_rtrim();
        let mut bytes = Vec::with_capacity(slice.len() * 8);
        bytes.extend(slice.iter().flat_map(|&word| word.to_le_bytes()));
        Cow::Owned(bytes)
    }

    /// Constructs a bitmap from little-endian bytes.
    ///
    /// # Examples
    ///
    /// ```
    /// use smol_bitmap::SmolBitmap;
    ///
    /// let bytes = [0b10000001, 0b00000001, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00];
    /// let (bitmap, _rest) = SmolBitmap::from_le_bytes(&bytes);
    ///
    /// assert!(bitmap.get(0)); // bit 0 from byte 0
    /// assert!(bitmap.get(7)); // bit 7 from byte 0
    /// assert!(bitmap.get(8)); // bit 0 from byte 1
    /// ```
    #[must_use]
    pub fn from_le_bytes(bytes: &[u8]) -> (Self, &[u8]) {
        let (words, rest) = bytes.as_chunks::<8>();
        let builder = words
            .iter()
            .map(|&w| u64::from_le_bytes(w))
            .collect::<SmolBitmapBuilder>();
        (builder.into(), rest)
    }
}
