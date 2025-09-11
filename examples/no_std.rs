//! Example demonstrating `no_std` usage with `SmolBitmap`
// #![no_std]

extern crate alloc;
use core::hint;

use alloc::{vec, vec::Vec};
use smol_bitmap::SmolBitmap;

fn main() {
    // Create a bitmap - works the same in no_std
    let mut bitmap = SmolBitmap::new();

    // Set some bits
    bitmap.insert(5);
    bitmap.insert(10);
    bitmap.insert(15);

    // Count set bits
    let count = bitmap.count_ones();
    // println!("Set bits: {count}");
    hint::black_box(count);

    // Create from iterator - uses alloc::vec
    let vec: Vec<usize> = vec![1, 3, 5, 7, 9];
    let from_vec: SmolBitmap = vec.into_iter().collect();

    // Perform set operations
    let union = bitmap.union(&from_vec);
    // println!("Union has {} bits set", union.count_ones());
    hint::black_box(union.count_ones());

    // Even large bitmaps work (they use alloc for heap storage)
    let mut large = SmolBitmap::new();
    large.insert(1000);
    // println!("Large bitmap spilled to heap: {}", large.is_spilled());
    hint::black_box(large.is_spilled());

    // All operations work the same as in std environments
    for bit in bitmap.iter().take(3) {
        // println!("Bit {bit} is set");
        hint::black_box(bit);
    }
}
