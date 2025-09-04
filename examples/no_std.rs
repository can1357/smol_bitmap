//! Example demonstrating `no_std` usage with `SmolBitmap`
// #![no_std]

extern crate alloc;
use alloc::{vec, vec::Vec};
use smol_bitmap::SmolBitmap;

fn main() {
    // Create a bitmap - works the same in no_std
    let mut bitmap = SmolBitmap::new();

    // Set some bits
    bitmap.set(5, true);
    bitmap.set(10, true);
    bitmap.set(15, true);

    // Count set bits
    let count = bitmap.count_ones();
    // println!("Set bits: {count}");
    core::hint::black_box(count);

    // Create from iterator - uses alloc::vec
    let vec: Vec<usize> = vec![1, 3, 5, 7, 9];
    let from_vec: SmolBitmap = vec.into_iter().collect();

    // Perform set operations
    let union = bitmap.union(&from_vec);
    // println!("Union has {} bits set", union.count_ones());
    core::hint::black_box(union.count_ones());

    // Even large bitmaps work (they use alloc for heap storage)
    let mut large = SmolBitmap::new();
    large.set(1000, true);
    // println!("Large bitmap spilled to heap: {}", large.is_spilled());
    core::hint::black_box(large.is_spilled());

    // All operations work the same as in std environments
    for bit in bitmap.iter().take(3) {
        // println!("Bit {bit} is set");
        core::hint::black_box(bit);
    }
}
