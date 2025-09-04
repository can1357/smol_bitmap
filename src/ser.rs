//! Serialization support for `SmolBitmap` using serde.

use core::fmt;

use serde::{Deserialize, Serialize};

use crate::{SmolBitmap, storage::SmolBitmapBuilder};

impl Serialize for SmolBitmap {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        let slice = self.as_slice_rtrim();
        slice.serialize(serializer)
    }
}

impl<'de> Deserialize<'de> for SmolBitmap {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        struct SmolBitmapVisitor;

        impl<'de> serde::de::Visitor<'de> for SmolBitmapVisitor {
            type Value = SmolBitmap;

            fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                formatter.write_str("a sequence of u64 words")
            }

            fn visit_seq<A>(self, mut seq: A) -> Result<Self::Value, A::Error>
            where
                A: serde::de::SeqAccess<'de>,
            {
                let mut builder = SmolBitmapBuilder::with_capacity(seq.size_hint().unwrap_or(0));
                while let Some(word) = seq.next_element::<u64>()? {
                    builder.push(word);
                }
                Ok(builder.finalize())
            }
        }

        deserializer.deserialize_seq(SmolBitmapVisitor)
    }
}
