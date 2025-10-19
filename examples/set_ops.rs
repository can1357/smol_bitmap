//! Demonstrates set operations with `SmolBitmap`
#![allow(clippy::many_single_char_names)]

use smol_bitmap::SmolBitmap;

fn main() {
    println!("=== SmolBitmap Set Operations ===\n");

    // Create two bitmaps
    let mut a = SmolBitmap::new();
    let mut b = SmolBitmap::new();

    // Populate bitmap A: {1, 2, 3, 5, 8}
    for i in [1, 2, 3, 5, 8] {
        a.insert(i);
    }

    // Populate bitmap B: {2, 3, 5, 7, 11}
    for i in [2, 3, 5, 7, 11] {
        b.insert(i);
    }

    println!("Set A: {:?}", a.iter().collect::<Vec<_>>());
    println!("Set B: {:?}", b.iter().collect::<Vec<_>>());
    println!();

    // Union (A ∪ B)
    let union = a.union(&b);
    println!("Union (A ∪ B): {:?}", union.iter().collect::<Vec<_>>());
    println!("Expected: [1, 2, 3, 5, 7, 8, 11]\n");

    // Intersection (A ∩ B)
    let intersection = a.intersection(&b);
    println!(
        "Intersection (A ∩ B): {:?}",
        intersection.iter().collect::<Vec<_>>()
    );
    println!("Expected: [2, 3, 5]\n");

    // Difference (A - B)
    let difference = a.difference(&b);
    println!(
        "Difference (A - B): {:?}",
        difference.iter().collect::<Vec<_>>()
    );
    println!("Expected: [1, 8]\n");

    // Symmetric Difference (A △ B)
    let sym_diff = a.symmetric_difference(&b);
    println!(
        "Symmetric Difference (A △ B): {:?}",
        sym_diff.iter().collect::<Vec<_>>()
    );
    println!("Expected: [1, 7, 8, 11]\n");

    // Set comparisons
    println!("=== Set Comparisons ===\n");

    let mut subset = SmolBitmap::new();
    for i in [2, 3] {
        subset.insert(i);
    }

    println!("Subset: {:?}", subset.iter().collect::<Vec<_>>());
    println!("Is subset ⊆ A? {}", subset.is_subset(&a));
    println!("Is A ⊇ subset? {}", a.is_superset(&subset));
    println!("Are A and B disjoint? {}", a.is_disjoint(&b));

    let mut disjoint = SmolBitmap::new();
    for i in [20, 30, 40] {
        disjoint.insert(i);
    }
    println!("\nDisjoint set: {:?}", disjoint.iter().collect::<Vec<_>>());
    println!(
        "Are A and disjoint set disjoint? {}",
        a.is_disjoint(&disjoint)
    );

    // In-place operations
    println!("\n=== In-place Operations ===\n");

    let mut c = a.clone();
    println!("C (copy of A): {:?}", c.iter().collect::<Vec<_>>());

    c.union_with(&b);
    println!("After C.union_with(B): {:?}", c.iter().collect::<Vec<_>>());

    let mut d = a.clone();
    d.intersection_with(&b);
    println!(
        "After D.intersection_with(B): {:?}",
        d.iter().collect::<Vec<_>>()
    );

    let mut e = a.clone();
    e.difference_with(&b);
    println!(
        "After E.difference_with(B): {:?}",
        e.iter().collect::<Vec<_>>()
    );

    // Complement example
    println!("\n=== Complement Operation ===\n");

    let mut bits = SmolBitmap::new();
    bits.insert(1);
    bits.insert(3);
    bits.insert(5);

    println!("Original: {:?}", bits.iter().collect::<Vec<_>>());

    bits.complement_range(0, 8);
    println!(
        "Complement up to bit 7: {:?}",
        bits.iter().collect::<Vec<_>>()
    );
    println!("Expected: [0, 2, 4, 6, 7]");
}
