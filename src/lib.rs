//! A space-efficient bitmap implementation with inline storage optimization.
//!
//! This crate provides [`SmolBitmap`], a bitmap that stores bits either inline
//! (for small bitmaps up to 127 bits) or on the heap (for larger bitmaps). The
//! implementation uses a clever encoding scheme where the highest bit of the
//! last word indicates whether the storage is inline or external.
//!
//! # Features
//!
//! - **Zero allocation** for bitmaps up to 127 bits
//! - **Automatic promotion** to heap storage when needed
//! - **Efficient set operations** (union, intersection, difference, symmetric
//!   difference)
//! - **Iterator support** for bit positions
//! - **Serialization support** via serde (optional)
//! - **`no_std` support** with `alloc` for embedded systems
//!
//! # Examples
//!
//! ```
//! use smol_bitmap::SmolBitmap;
//!
//! // Create a new bitmap
//! let mut bitmap = SmolBitmap::new();
//!
//! // Set some bits
//! bitmap.insert(10);
//! bitmap.insert(42);
//! bitmap.insert(127); // Still inline!
//!
//! // Check if bits are set
//! assert!(bitmap.get(10));
//! assert!(!bitmap.get(11));
//!
//! // Iterate over set bits
//! for bit in bitmap.iter() {
//!     println!("Bit {} is set", bit);
//! }
//!
//! // Set operations
//! let mut other = SmolBitmap::new();
//! other.insert(10);
//! other.insert(50);
//!
//! let union = bitmap.union(&other);
//! let intersection = bitmap.intersection(&other);
//! ```
//!
//! # Storage Strategy
//!
//! The bitmap uses a hybrid storage strategy:
//!
//! - **Inline storage**: Up to 127 bits stored directly in the struct (16
//!   bytes)
//! - **Heap storage**: Automatically switches to heap allocation for larger
//!   bitmaps
//!
//! The transition is completely transparent to the user.
//!
//! # Performance
//!
//! `SmolBitmap` is optimized for the common case of small bitmaps while still
//! supporting arbitrary sizes efficiently. Key performance characteristics:
//!
//! - Setting/getting bits is O(1)
//! - Set operations are O(n) where n is the number of words
//! - No allocation overhead for bitmaps ≤ 127 bits
//! - Memory-efficient for sparse bitmaps

#![cfg_attr(not(feature = "std"), no_std)]
#![warn(missing_docs)]

extern crate alloc;

// Module declarations
mod bitmap;
mod iter;
mod macros;
mod ser;
mod set_ops;
pub mod storage;
pub mod traits;

#[cfg(feature = "rkyv")]
pub mod rkyv;

#[cfg(feature = "rkyv")]
pub use rkyv::{ArchivedSmolBitmap, SmolBitmapResolver};

#[cfg(feature = "serde")]
pub mod serde;

// Re-exports
pub use bitmap::SmolBitmap;
pub use iter::{BitIter, IntoIter, Iter, SelectIter};
pub use storage::SmolBitmapBuilder;
pub use traits::{ParseBitmapError, TryFromBitmapError};
