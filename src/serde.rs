//! Serde implementations for `SmolBitmap`.

use super::{SmolBitmap, SmolBitmapBuilder};
use serde::{
    Deserialize, Deserializer, Serialize, Serializer,
    de::{self, SeqAccess, Visitor},
    ser::SerializeSeq,
};

/// Serde implementation serializing the bitmap as a sequence of u64 words.
pub mod words {
    use super::*;

    /// Serialize the bitmap as a sequence of u64 words.
    pub fn serialize<S>(b: &SmolBitmap, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let slice: &[u64] = b.as_slice_rtrim();
        slice.serialize(serializer)
    }

    /// Deserialize the bitmap from a sequence of u64 words.
    pub fn deserialize<'de, D>(deserializer: D) -> Result<SmolBitmap, D::Error>
    where
        D: Deserializer<'de>,
    {
        struct SmolBitmapVisitor;

        impl<'de> Visitor<'de> for SmolBitmapVisitor {
            type Value = SmolBitmap;

            fn expecting(&self, formatter: &mut core::fmt::Formatter) -> core::fmt::Result {
                formatter.write_str("a sequence of u64 words")
            }

            fn visit_seq<A>(self, mut seq: A) -> Result<Self::Value, A::Error>
            where
                A: SeqAccess<'de>,
            {
                let mut builder = SmolBitmapBuilder::with_capacity(seq.size_hint().unwrap_or(0));
                while let Some(word) = seq.next_element::<u64>()? {
                    builder.push(word);
                }
                Ok(builder.into())
            }
        }

        deserializer.deserialize_seq(SmolBitmapVisitor)
    }
}

/// Module for serializing and deserializing [`SmolBitmap`] as a sorted set of
/// integers.
pub mod sorted_set {
    use super::*;

    /// Serialize the [`SmolBitmap`] as a sorted sequence of integers.
    ///
    /// This function serializes the bitmap by iterating over its set bits
    /// and writing each index as an element in the sequence.
    ///
    /// # Errors
    ///
    /// Returns an error if the serializer fails to serialize the sequence.
    pub fn serialize<S>(b: &SmolBitmap, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let n = b.cardinality();
        let mut ser = serializer.serialize_seq(Some(n))?;
        for i in b.iter() {
            ser.serialize_element(&i)?;
        }
        ser.end()
    }

    /// Deserialize a [`SmolBitmap`] from a sorted sequence of integers.
    ///
    /// This function expects a sorted sequence of integers, where each integer
    /// represents an index of a set bit in the bitmap.
    ///
    /// # Errors
    ///
    /// Returns an error if the sequence is not sorted or if deserialization
    /// fails.
    pub fn deserialize<'de, D>(deserializer: D) -> Result<SmolBitmap, D::Error>
    where
        D: Deserializer<'de>,
    {
        struct SmolBitmapVisitor;

        impl<'de> Visitor<'de> for SmolBitmapVisitor {
            type Value = SmolBitmap;

            fn expecting(&self, formatter: &mut core::fmt::Formatter) -> core::fmt::Result {
                formatter.write_str("a sorted sequence of integers")
            }

            fn visit_seq<A>(self, mut seq: A) -> Result<Self::Value, A::Error>
            where
                A: SeqAccess<'de>,
            {
                let mut b = SmolBitmap::new();
                let mut last = None;
                while let Some(word) = seq.next_element::<usize>()? {
                    if let Some(last) = last
                        && last >= word
                    {
                        return Err(de::Error::invalid_value(
                            de::Unexpected::Unsigned(word as u64),
                            &"sorted sequence",
                        ));
                    }
                    last = Some(word);
                    b.insert(word);
                }
                Ok(b)
            }
        }

        deserializer.deserialize_seq(SmolBitmapVisitor)
    }
}

/// Module for serializing and deserializing [`SmolBitmap`] as an unordered set
/// of integers.
pub mod unordered_set {
    use super::*;

    /// Serialize the [`SmolBitmap`] as an unordered sequence of integers.
    ///
    /// This function serializes the bitmap by iterating over its set bits
    /// and writing each index as an element in the sequence.
    ///
    /// # Errors
    ///
    /// Returns an error if the serializer fails to serialize the sequence.
    pub fn serialize<S>(b: &SmolBitmap, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        sorted_set::serialize(b, serializer)
    }

    /// Deserialize a [`SmolBitmap`] from an unordered sequence of integers.
    ///
    /// This function expects a sorted sequence of integers, where each integer
    /// represents an index of a set bit in the bitmap.
    ///
    /// # Errors
    ///
    /// Returns an error if the sequence is not sorted or if deserialization
    /// fails.
    pub fn deserialize<'de, D>(deserializer: D) -> Result<SmolBitmap, D::Error>
    where
        D: Deserializer<'de>,
    {
        struct SmolBitmapVisitor;

        impl<'de> Visitor<'de> for SmolBitmapVisitor {
            type Value = SmolBitmap;

            fn expecting(&self, formatter: &mut core::fmt::Formatter) -> core::fmt::Result {
                formatter.write_str("a sequence of integers")
            }

            fn visit_seq<A>(self, mut seq: A) -> Result<Self::Value, A::Error>
            where
                A: SeqAccess<'de>,
            {
                let mut b = SmolBitmap::new();
                while let Some(word) = seq.next_element::<usize>()? {
                    b.insert(word);
                }
                Ok(b)
            }
        }

        deserializer.deserialize_seq(SmolBitmapVisitor)
    }
}

/// Macro to implement byte-based serialization and deserialization for
/// [`SmolBitmap`].
macro_rules! impl_bytes {
    ($mod:ident, $from_fn:ident, $to_fn:ident, $doc:literal) => {
        #[doc = $doc]
        pub mod $mod {
            use super::*;

            /// Serialize the [`SmolBitmap`] as bytes.
            ///
            /// This function serializes the bitmap's internal byte representation.
            ///
            /// # Errors
            ///
            /// Returns an error if the serializer fails to serialize the bytes.
            pub fn serialize<S>(b: &SmolBitmap, serializer: S) -> Result<S::Ok, S::Error>
            where
                S: Serializer,
            {
                binser::serialize(b.$to_fn().as_ref(), serializer)
            }

            /// Deserialize a [`SmolBitmap`] from bytes.
            ///
            /// This function expects a byte slice that represents the bitmap.
            ///
            /// # Errors
            ///
            /// Returns an error if the byte slice length is not a multiple of 8 or if
            /// deserialization fails.
            pub fn deserialize<'de, D>(deserializer: D) -> Result<SmolBitmap, D::Error>
            where
                D: Deserializer<'de>,
            {
                binser::deserialize(
                    deserializer,
                    #[inline(always)]
                    |bytes| SmolBitmap::$from_fn(bytes),
                )
            }
        }
    };
}

// Implementations for native-endian, little-endian, and big-endian byte orders.
impl_bytes!(
    ne_bytes,
    from_ne_bytes,
    to_ne_bytes,
    "Serialize and deserialize [`SmolBitmap`] using native-endian byte order."
);
impl_bytes!(
    le_bytes,
    from_le_bytes,
    to_le_bytes,
    "Serialize and deserialize [`SmolBitmap`] using little-endian byte order."
);
impl_bytes!(
    be_bytes,
    from_be_bytes,
    to_be_bytes,
    "Serialize and deserialize [`SmolBitmap`] using big-endian byte order."
);

impl Serialize for SmolBitmap {
    /// Serialize the [`SmolBitmap`] using little-endian byte order.
    ///
    /// # Errors
    ///
    /// Returns an error if serialization fails.
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        le_bytes::serialize(self, serializer)
    }
}

impl<'de> Deserialize<'de> for SmolBitmap {
    /// Deserialize a [`SmolBitmap`] using little-endian byte order.
    ///
    /// # Errors
    ///
    /// Returns an error if deserialization fails.
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        le_bytes::deserialize(deserializer)
    }
}

/// Helper module for base64 serialization
mod binser {
    use super::*;

    /// Serialize the [`SmolBitmap`] as bytes.
    ///
    /// This function serializes the bitmap's internal byte representation.
    ///
    /// # Errors
    ///
    /// Returns an error if the serializer fails to serialize the bytes.
    pub fn serialize<S>(bytes: &[u8], serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        if serializer.is_human_readable() {
            let encoded = data_encoding::BASE64.encode(bytes);
            serializer.serialize_str(&encoded)
        } else {
            serializer.serialize_bytes(bytes)
        }
    }

    /// Deserialize a [`SmolBitmap`] from bytes.
    ///
    /// This function expects a byte slice that represents the bitmap.
    ///
    /// # Errors
    ///
    /// Returns an error if the byte slice length is not a multiple of 8 or if
    /// deserialization fails.
    pub fn deserialize<'de, D, P>(deserializer: D, parse: P) -> Result<SmolBitmap, D::Error>
    where
        D: Deserializer<'de>,
        P: FnOnce(&[u8]) -> (SmolBitmap, &[u8]),
    {
        if deserializer.is_human_readable() {
            struct SmolBitmapVisitor<P>(P);

            impl<'de, P> Visitor<'de> for SmolBitmapVisitor<P>
            where
                P: FnOnce(&[u8]) -> (SmolBitmap, &[u8]),
            {
                type Value = SmolBitmap;

                fn expecting(&self, formatter: &mut core::fmt::Formatter) -> core::fmt::Result {
                    formatter.write_str("bytes representation of a bitmap")
                }

                fn visit_str<E>(self, v: &str) -> Result<Self::Value, E>
                where
                    E: de::Error,
                {
                    let decoded = data_encoding::BASE64
                        .decode(v.as_bytes())
                        .map_err(E::custom)?;
                    let (bitmap, leftover) = (self.0)(&decoded);
                    if !leftover.is_empty() {
                        return Err(de::Error::invalid_length(
                            decoded.len(),
                            &"multiple of 8 bytes",
                        ));
                    }
                    Ok(bitmap)
                }
            }

            deserializer.deserialize_str(SmolBitmapVisitor(parse))
        } else {
            struct SmolBitmapVisitor<P>(P);

            impl<'de, P> Visitor<'de> for SmolBitmapVisitor<P>
            where
                P: FnOnce(&[u8]) -> (SmolBitmap, &[u8]),
            {
                type Value = SmolBitmap;

                fn expecting(&self, formatter: &mut core::fmt::Formatter) -> core::fmt::Result {
                    formatter.write_str("bytes representation of a bitmap")
                }

                fn visit_bytes<E>(self, v: &[u8]) -> Result<Self::Value, E>
                where
                    E: de::Error,
                {
                    if !v.len().is_multiple_of(8) {
                        return Err(de::Error::invalid_length(v.len(), &"multiple of 8 bytes"));
                    }
                    let (bitmap, _) = (self.0)(v);
                    Ok(bitmap)
                }
            }

            deserializer.deserialize_bytes(SmolBitmapVisitor(parse))
        }
    }
}

#[cfg(all(test, feature = "serde"))]
mod tests {
    use super::*;
    use ::serde::{Deserialize, Serialize};
    use serde_test::{Token, assert_tokens};

    // Helper struct for testing different serde formats
    #[derive(Debug, Serialize, Deserialize, PartialEq)]
    struct WordsWrapper {
        #[serde(with = "words")]
        bitmap: SmolBitmap,
    }

    #[derive(Debug, Serialize, Deserialize, PartialEq)]
    struct SortedSetWrapper {
        #[serde(with = "sorted_set")]
        bitmap: SmolBitmap,
    }

    #[derive(Debug, Serialize, Deserialize, PartialEq)]
    struct UnorderedSetWrapper {
        #[serde(with = "unordered_set")]
        bitmap: SmolBitmap,
    }

    #[derive(Debug, Serialize, Deserialize, PartialEq)]
    struct NeBytesWrapper {
        #[serde(with = "ne_bytes")]
        bitmap: SmolBitmap,
    }

    #[derive(Debug, Serialize, Deserialize, PartialEq)]
    struct LeBytesWrapper {
        #[serde(with = "le_bytes")]
        bitmap: SmolBitmap,
    }

    #[derive(Debug, Serialize, Deserialize, PartialEq)]
    struct BeBytesWrapper {
        #[serde(with = "be_bytes")]
        bitmap: SmolBitmap,
    }

    // ========================================================================
    // Words format tests
    // ========================================================================

    #[test]
    fn test_words_empty() {
        let bitmap = SmolBitmap::new();
        let wrapper = WordsWrapper { bitmap };

        assert_tokens(
            &wrapper,
            &[
                Token::Struct {
                    name: "WordsWrapper",
                    len: 1,
                },
                Token::Str("bitmap"),
                Token::Seq { len: Some(0) },
                Token::SeqEnd,
                Token::StructEnd,
            ],
        );
    }

    #[test]
    fn test_words_single_word() {
        let mut bitmap = SmolBitmap::new();
        bitmap.insert(0);
        bitmap.insert(63);
        let wrapper = WordsWrapper { bitmap };

        assert_tokens(
            &wrapper,
            &[
                Token::Struct {
                    name: "WordsWrapper",
                    len: 1,
                },
                Token::Str("bitmap"),
                Token::Seq { len: Some(1) },
                Token::U64((1u64 << 63) | 1),
                Token::SeqEnd,
                Token::StructEnd,
            ],
        );
    }

    #[test]
    fn test_words_multiple_words() {
        let mut bitmap = SmolBitmap::new();
        bitmap.insert(0);
        bitmap.insert(64);
        let wrapper = WordsWrapper { bitmap };

        // Should serialize to at least 2 words
        let serialized = serde_json::to_string(&wrapper).unwrap();
        let deserialized: WordsWrapper = serde_json::from_str(&serialized).unwrap();

        assert!(deserialized.bitmap.get(0));
        assert!(deserialized.bitmap.get(64));
    }

    #[test]
    fn test_words_roundtrip_large() {
        let mut bitmap = SmolBitmap::new();
        // Create a pattern that requires external storage
        for i in (0..300).step_by(3) {
            bitmap.insert(i);
        }

        let wrapper = WordsWrapper {
            bitmap: bitmap.clone(),
        };
        let serialized = serde_json::to_string(&wrapper).unwrap();
        let deserialized: WordsWrapper = serde_json::from_str(&serialized).unwrap();

        for i in 0..300 {
            assert_eq!(deserialized.bitmap.get(i), bitmap.get(i));
        }
    }

    // ========================================================================
    // Sorted set format tests
    // ========================================================================

    #[test]
    fn test_sorted_set_empty() {
        let bitmap = SmolBitmap::new();
        let wrapper = SortedSetWrapper { bitmap };

        assert_tokens(
            &wrapper,
            &[
                Token::Struct {
                    name: "SortedSetWrapper",
                    len: 1,
                },
                Token::Str("bitmap"),
                Token::Seq { len: Some(0) },
                Token::SeqEnd,
                Token::StructEnd,
            ],
        );
    }

    #[test]
    fn test_sorted_set_single_bit() {
        let mut bitmap = SmolBitmap::new();
        bitmap.insert(42);
        let wrapper = SortedSetWrapper { bitmap };

        assert_tokens(
            &wrapper,
            &[
                Token::Struct {
                    name: "SortedSetWrapper",
                    len: 1,
                },
                Token::Str("bitmap"),
                Token::Seq { len: Some(1) },
                Token::U64(42),
                Token::SeqEnd,
                Token::StructEnd,
            ],
        );
    }

    #[test]
    fn test_sorted_set_multiple_bits() {
        let mut bitmap = SmolBitmap::new();
        bitmap.insert(5);
        bitmap.insert(10);
        bitmap.insert(15);
        let wrapper = SortedSetWrapper { bitmap };

        assert_tokens(
            &wrapper,
            &[
                Token::Struct {
                    name: "SortedSetWrapper",
                    len: 1,
                },
                Token::Str("bitmap"),
                Token::Seq { len: Some(3) },
                Token::U64(5),
                Token::U64(10),
                Token::U64(15),
                Token::SeqEnd,
                Token::StructEnd,
            ],
        );
    }

    #[test]
    fn test_sorted_set_deserialize_unsorted_fails() {
        let json = r#"{"bitmap": [10, 5, 15]}"#;
        let result: Result<SortedSetWrapper, _> = serde_json::from_str(json);
        assert!(result.is_err());
    }

    #[test]
    fn test_sorted_set_roundtrip() {
        let mut bitmap = SmolBitmap::new();
        for i in [1, 5, 10, 63, 64, 100] {
            bitmap.insert(i);
        }

        let wrapper = SortedSetWrapper {
            bitmap: bitmap.clone(),
        };
        let serialized = serde_json::to_string(&wrapper).unwrap();
        let deserialized: SortedSetWrapper = serde_json::from_str(&serialized).unwrap();

        for i in 0..=100 {
            assert_eq!(deserialized.bitmap.get(i), bitmap.get(i));
        }
    }

    // ========================================================================
    // Unordered set format tests
    // ========================================================================

    #[test]
    fn test_unordered_set_empty() {
        let bitmap = SmolBitmap::new();
        let wrapper = UnorderedSetWrapper { bitmap };

        let serialized = serde_json::to_string(&wrapper).unwrap();
        assert_eq!(serialized, r#"{"bitmap":[]}"#);
    }

    #[test]
    fn test_unordered_set_accepts_unsorted() {
        // This should succeed unlike sorted_set
        let json = r#"{"bitmap": [10, 5, 15, 5]}"#; // Note: includes duplicate
        let deserialized: UnorderedSetWrapper = serde_json::from_str(json).unwrap();

        assert!(deserialized.bitmap.get(5));
        assert!(deserialized.bitmap.get(10));
        assert!(deserialized.bitmap.get(15));
        assert_eq!(deserialized.bitmap.count_ones(), 3); // Duplicate is handled correctly
    }

    #[test]
    fn test_unordered_set_roundtrip() {
        let mut bitmap = SmolBitmap::new();
        for i in [100, 5, 63, 1, 10, 64] {
            bitmap.insert(i);
        }

        let wrapper = UnorderedSetWrapper {
            bitmap: bitmap.clone(),
        };
        let serialized = serde_json::to_string(&wrapper).unwrap();
        let deserialized: UnorderedSetWrapper = serde_json::from_str(&serialized).unwrap();

        for i in 0..=100 {
            assert_eq!(deserialized.bitmap.get(i), bitmap.get(i));
        }
    }

    // ========================================================================
    // Byte format tests
    // ========================================================================

    #[test]
    fn test_le_bytes_empty() {
        let bitmap = SmolBitmap::new();
        let wrapper = LeBytesWrapper { bitmap };

        let serialized = postcard::to_allocvec(&wrapper).unwrap();
        let deserialized: LeBytesWrapper = postcard::from_bytes(&serialized).unwrap();

        assert_eq!(deserialized.bitmap.count_ones(), 0);
    }

    #[test]
    fn test_le_bytes_roundtrip() {
        let mut bitmap = SmolBitmap::new();
        bitmap.insert(0);
        bitmap.insert(7);
        bitmap.insert(8);
        bitmap.insert(15);
        bitmap.insert(64);

        let wrapper = LeBytesWrapper {
            bitmap: bitmap.clone(),
        };
        let serialized = postcard::to_allocvec(&wrapper).unwrap();
        let deserialized: LeBytesWrapper = postcard::from_bytes(&serialized).unwrap();

        for i in 0..=100 {
            assert_eq!(deserialized.bitmap.get(i), bitmap.get(i));
        }
    }

    #[test]
    fn test_be_bytes_roundtrip() {
        let mut bitmap = SmolBitmap::new();
        bitmap.insert(0);
        bitmap.insert(63);
        bitmap.insert(64);
        bitmap.insert(127);

        let wrapper = BeBytesWrapper {
            bitmap: bitmap.clone(),
        };
        let serialized = postcard::to_allocvec(&wrapper).unwrap();
        let deserialized: BeBytesWrapper = postcard::from_bytes(&serialized).unwrap();

        for i in 0..=127 {
            assert_eq!(deserialized.bitmap.get(i), bitmap.get(i));
        }
    }

    #[test]
    fn test_ne_bytes_roundtrip() {
        let mut bitmap = SmolBitmap::new();
        for i in (0..200).step_by(7) {
            bitmap.insert(i);
        }

        let wrapper = NeBytesWrapper {
            bitmap: bitmap.clone(),
        };
        let serialized = postcard::to_allocvec(&wrapper).unwrap();
        let deserialized: NeBytesWrapper = postcard::from_bytes(&serialized).unwrap();

        for i in 0..200 {
            assert_eq!(deserialized.bitmap.get(i), bitmap.get(i));
        }
    }

    // ========================================================================
    // Default implementation tests
    // ========================================================================

    #[test]
    fn test_default_impl_uses_le_bytes() {
        let mut bitmap = SmolBitmap::new();
        bitmap.insert(0);
        bitmap.insert(63);
        bitmap.insert(64);

        // Default implementation should use le_bytes
        let serialized = postcard::to_allocvec(&bitmap).unwrap();
        let deserialized: SmolBitmap = postcard::from_bytes(&serialized).unwrap();

        assert!(deserialized.get(0));
        assert!(deserialized.get(63));
        assert!(deserialized.get(64));
    }

    #[test]
    fn test_default_impl_json() {
        let mut bitmap = SmolBitmap::new();
        bitmap.insert(10);
        bitmap.insert(20);

        // JSON serialization with default implementation
        let json = serde_json::to_string(&bitmap).unwrap();
        let deserialized: SmolBitmap = serde_json::from_str(&json).unwrap();
        println!("json: {json}");
        println!("deserialized: {deserialized:?}");
        assert!(deserialized.get(10));
        assert!(deserialized.get(20));
        assert_eq!(deserialized.count_ones(), 2);
    }

    // ========================================================================
    // Cross-format compatibility tests
    // ========================================================================

    #[test]
    fn test_words_to_sorted_set_conversion() {
        // Create bitmap and serialize as words
        let mut bitmap = SmolBitmap::new();
        bitmap.insert(5);
        bitmap.insert(10);
        bitmap.insert(15);

        let words_wrapper = WordsWrapper {
            bitmap: bitmap.clone(),
        };
        let words_json = serde_json::to_value(&words_wrapper).unwrap();

        // Verify the words format
        assert!(words_json["bitmap"].is_array());

        // Create the same bitmap via sorted set
        let sorted_wrapper = SortedSetWrapper { bitmap };
        let sorted_json = serde_json::to_value(&sorted_wrapper).unwrap();

        // They should represent the same data differently
        assert_ne!(words_json["bitmap"], sorted_json["bitmap"]);
    }

    // ========================================================================
    // Edge cases and stress tests
    // ========================================================================

    #[test]
    fn test_very_large_bitmap() {
        let mut bitmap = SmolBitmap::new();

        // Create a sparse bitmap with bits set at powers of 2
        for i in 0..10 {
            bitmap.insert(1 << i);
        }

        // Test all formats
        let words_wrapper = WordsWrapper {
            bitmap: bitmap.clone(),
        };
        let sorted_wrapper = SortedSetWrapper {
            bitmap: bitmap.clone(),
        };
        let unordered_wrapper = UnorderedSetWrapper {
            bitmap: bitmap.clone(),
        };
        let le_wrapper = LeBytesWrapper {
            bitmap: bitmap.clone(),
        };

        // Serialize and deserialize each format
        let w_json = serde_json::to_string(&words_wrapper).unwrap();
        let s_json = serde_json::to_string(&sorted_wrapper).unwrap();
        let u_json = serde_json::to_string(&unordered_wrapper).unwrap();
        let l_bytes = postcard::to_allocvec(&le_wrapper).unwrap();

        let w_deser: WordsWrapper = serde_json::from_str(&w_json).unwrap();
        let s_deser: SortedSetWrapper = serde_json::from_str(&s_json).unwrap();
        let u_deser: UnorderedSetWrapper = serde_json::from_str(&u_json).unwrap();
        let l_deser: LeBytesWrapper = postcard::from_bytes(&l_bytes).unwrap();

        // Verify all deserializations are correct
        for i in 0..10 {
            let bit_pos = 1 << i;
            assert!(w_deser.bitmap.get(bit_pos));
            assert!(s_deser.bitmap.get(bit_pos));
            assert!(u_deser.bitmap.get(bit_pos));
            assert!(l_deser.bitmap.get(bit_pos));
        }
    }

    #[test]
    fn test_all_bits_in_word() {
        let mut bitmap = SmolBitmap::new();

        // Set all bits in first word
        for i in 0..64 {
            bitmap.insert(i);
        }

        let wrapper = WordsWrapper {
            bitmap: bitmap.clone(),
        };
        let serialized = serde_json::to_string(&wrapper).unwrap();
        let deserialized: WordsWrapper = serde_json::from_str(&serialized).unwrap();

        assert_eq!(deserialized.bitmap.count_ones(), 64);
        for i in 0..64 {
            assert!(deserialized.bitmap.get(i));
        }
    }

    #[test]
    fn test_sparse_bitmap() {
        let mut bitmap = SmolBitmap::new();

        // Very sparse bitmap
        bitmap.insert(0);
        bitmap.insert(1000);
        bitmap.insert(10000);

        // sorted_set should be efficient for sparse bitmaps
        let sorted_wrapper = SortedSetWrapper {
            bitmap: bitmap.clone(),
        };
        let json = serde_json::to_string(&sorted_wrapper).unwrap();

        // Should serialize as just 3 numbers
        assert!(json.contains("[0,1000,10000]"));

        let deserialized: SortedSetWrapper = serde_json::from_str(&json).unwrap();
        assert!(deserialized.bitmap.get(0));
        assert!(deserialized.bitmap.get(1000));
        assert!(deserialized.bitmap.get(10000));
        assert_eq!(deserialized.bitmap.count_ones(), 3);
    }

    #[test]
    fn test_endianness_differences() {
        let mut bitmap = SmolBitmap::new();
        bitmap.insert(0);
        bitmap.insert(7); // Within first byte
        bitmap.insert(8); // Second byte
        bitmap.insert(15); // Second byte

        let le_wrapper = LeBytesWrapper {
            bitmap: bitmap.clone(),
        };
        let be_wrapper = BeBytesWrapper {
            bitmap: bitmap.clone(),
        };

        let le_bytes = postcard::to_allocvec(&le_wrapper).unwrap();
        let be_bytes = postcard::to_allocvec(&be_wrapper).unwrap();

        // The byte representations should differ due to endianness
        // but both should deserialize to the same logical bitmap
        let le_deser: LeBytesWrapper = postcard::from_bytes(&le_bytes).unwrap();
        let be_deser: BeBytesWrapper = postcard::from_bytes(&be_bytes).unwrap();

        for i in 0..16 {
            assert_eq!(le_deser.bitmap.get(i), be_deser.bitmap.get(i));
        }
    }
}
