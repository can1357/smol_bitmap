//! Rkyv implementation for `SmolBitmap`.

use rkyv::{
    Archive, Deserialize, Serialize,
    rancor::Fallible,
    ser::{Allocator, Writer},
    vec::ArchivedVec,
};

use crate::{SmolBitmap, SmolBitmapBuilder};

/// The archived version of SmolBitmap.
pub type ArchivedSmolBitmap = ArchivedVec<<u64 as rkyv::Archive>::Archived>;

/// The resolver for SmolBitmap.
pub type SmolBitmapResolver = rkyv::vec::VecResolver;

// Manual Archive implementation for SmolBitmap
impl Archive for SmolBitmap {
    type Archived = ArchivedSmolBitmap;
    type Resolver = SmolBitmapResolver;

    fn resolve(&self, resolver: Self::Resolver, out: rkyv::Place<Self::Archived>) {
        let slice = self.as_slice_rtrim();
        ArchivedVec::resolve_from_slice(slice, resolver, out);
    }
}

// Serialize implementation
impl<S: Fallible + Allocator + Writer + ?Sized> Serialize<S> for SmolBitmap {
    #[inline]
    fn serialize(&self, serializer: &mut S) -> Result<Self::Resolver, S::Error> {
        let slice = self.as_slice_rtrim();
        ArchivedVec::<_>::serialize_from_slice(slice, serializer)
    }
}

// Deserialize implementation
impl<D: Fallible + ?Sized> Deserialize<SmolBitmap, D> for ArchivedSmolBitmap {
    #[inline]
    fn deserialize(&self, _deserializer: &mut D) -> Result<SmolBitmap, D::Error> {
        let slice = self.as_slice();
        let mut builder = SmolBitmapBuilder::with_capacity(slice.len());
        builder.extend(slice.iter().map(|w| w.to_native()));
        Ok(builder.into())
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_basic_archive() {
        let mut bitmap = SmolBitmap::new();
        bitmap.insert(5);
        bitmap.insert(10);
        bitmap.insert(100);

        // Serialize
        let bytes = rkyv::to_bytes::<rkyv::rancor::Error>(&bitmap).unwrap();

        // Deserialize back
        let deserialized: SmolBitmap =
            rkyv::api::high::from_bytes::<_, rkyv::rancor::Error>(&bytes).unwrap();
        assert_eq!(deserialized.get(5), bitmap.get(5));
        assert_eq!(deserialized.get(10), bitmap.get(10));
        assert_eq!(deserialized.get(100), bitmap.get(100));
    }
}
