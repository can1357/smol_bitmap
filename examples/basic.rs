//! Basic usage examples for `SmolBitmap`

use smol_bitmap::SmolBitmap;

fn main() {
    println!("=== SmolBitmap Basic Usage ===\n");

    // Create a new empty bitmap
    let mut bitmap = SmolBitmap::new();
    println!("Created new bitmap");
    println!("Initial capacity: {} bits", bitmap.capacity());
    println!("Is using heap storage? {}\n", bitmap.is_spilled());

    // Set some bits
    bitmap.insert(5);
    bitmap.insert(10);
    bitmap.insert(15);
    bitmap.insert(100);

    println!("Set bits at positions: 5, 10, 15, 100");
    println!("Number of set bits: {}", bitmap.count_ones());
    println!("Is using heap storage? {}\n", bitmap.is_spilled());

    // Check if specific bits are set
    println!("Checking individual bits:");
    for i in &[0, 5, 10, 15, 20, 100, 150] {
        println!(
            "  Bit {}: {}",
            i,
            if bitmap.get(*i) { "set" } else { "unset" }
        );
    }

    // Iterate over set bits
    println!("\nIterating over set bits:");
    print!("  Set bits: ");
    for bit in &bitmap {
        print!("{bit} ");
    }
    println!("\n");

    // Force heap allocation by setting a high bit
    println!("Setting bit at position 200 (forces heap allocation)");
    bitmap.insert(200);
    println!("Is using heap storage? {}", bitmap.is_spilled());
    println!("New capacity: {} bits\n", bitmap.capacity());

    // Complement some bits
    println!("Complementing bits at positions 5 and 25");
    bitmap.complement(5); // Was set, now unset
    bitmap.complement(25); // Was unset, now set

    println!("Updated set bits:");
    print!("  ");
    for bit in &bitmap {
        print!("{bit} ");
    }
    println!("\n");

    // Find first and last set bits
    if let Some(first) = bitmap.first() {
        println!("First set bit: {first}");
    }
    if let Some(last) = bitmap.last() {
        println!("Last set bit: {last}");
    }

    // Clear all bits
    println!("\nClearing all bits");
    bitmap.clear();
    println!("Number of set bits after clear: {}", bitmap.count_ones());
    println!("Is empty? {}", bitmap.is_empty());
}
