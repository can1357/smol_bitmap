//! Advanced usage patterns and features

use smol_bitmap::SmolBitmap;

fn main() {
    println!("=== SmolBitmap Advanced Features ===\n");

    // Creating from iterators
    println!("Creating from iterators:");
    let from_range: SmolBitmap = (0..10).step_by(2).collect();
    println!(
        "From range (0..10).step_by(2): {:?}",
        from_range.iter().collect::<Vec<_>>()
    );

    let from_vec: SmolBitmap = vec![5, 15, 25, 35].into_iter().collect();
    println!(
        "From vec [5, 15, 25, 35]: {:?}",
        from_vec.iter().collect::<Vec<_>>()
    );
    println!();

    // Extending bitmaps
    println!("Extending bitmaps:");
    let mut bitmap = SmolBitmap::new();
    bitmap.extend(vec![1, 2, 3]);
    println!("Initial: {:?}", bitmap.iter().collect::<Vec<_>>());

    bitmap.extend(vec![10, 20, 30]);
    println!(
        "After extending with [10, 20, 30]: {:?}",
        bitmap.iter().collect::<Vec<_>>()
    );
    println!();

    // Retain with predicate
    println!("Using retain() with predicate:");
    let mut bitmap = SmolBitmap::new();
    bitmap.extend(0..20);
    println!("All bits 0..20: {:?}", bitmap.iter().collect::<Vec<_>>());

    // Keep only numbers divisible by 3
    bitmap.retain(|bit| bit.is_multiple_of(3));
    println!(
        "After retain(divisible by 3): {:?}",
        bitmap.iter().collect::<Vec<_>>()
    );
    println!();

    // Finding adjacent set bits
    println!("Finding adjacent set bits:");
    let mut bitmap = SmolBitmap::new();
    for i in [5, 10, 15, 25, 40, 60] {
        bitmap.set(i, true);
    }
    println!("Bitmap: {:?}", bitmap.iter().collect::<Vec<_>>());

    // Find next set bit from position 12
    if let Some(next) = bitmap.next_set_bit(12) {
        println!("Next set bit from position 12: {next}");
    }

    // Find previous set bit from position 30
    if let Some(prev) = bitmap.prev_set_bit(30) {
        println!("Previous set bit from position 30: {prev}");
    }
    println!();

    // Working with capacity
    println!("Capacity management:");
    let mut bitmap = SmolBitmap::new();
    println!("Initial capacity: {}", bitmap.capacity());

    bitmap.reserve(500);
    println!("After reserve(500): {}", bitmap.capacity());
    println!("Spilled to heap? {}", bitmap.is_spilled());

    // Add some bits then shrink
    for i in 0..50 {
        bitmap.set(i, true);
    }
    bitmap.shrink_to_fit();
    println!(
        "After adding 50 bits and shrink_to_fit(): {}",
        bitmap.capacity()
    );
    println!();

    // Select iterator - selecting elements from another iterator
    println!("Select iterator:");
    let mut selector = SmolBitmap::new();
    selector.set(0, true); // Select 1st element (index 0)
    selector.set(2, true); // Select 3rd element (index 2)
    selector.set(4, true); // Select 5th element (index 4)

    let data = vec!["a", "b", "c", "d", "e", "f"];
    let selected: Vec<_> = selector.select(data).collect();
    println!("Selector bitmap: {:?}", selector.iter().collect::<Vec<_>>());
    println!("Selected elements: {selected:?}");
    println!();

    // Parsing from strings
    println!("Parsing from strings:");

    let binary: SmolBitmap = "0b1010".parse().unwrap();
    println!("Binary '0b1010': {:?}", binary.iter().collect::<Vec<_>>());

    let binary2: SmolBitmap = "0b1111".parse().unwrap();
    println!("Binary '0b1111': {:?}", binary2.iter().collect::<Vec<_>>());

    let binary_with_underscore: SmolBitmap = "0b1111_0000".parse().unwrap();
    println!(
        "Binary '0b1111_0000': {:?}",
        binary_with_underscore.iter().collect::<Vec<_>>()
    );
    println!();

    // Display formats
    println!("Display formats:");
    let mut bitmap = SmolBitmap::new();
    for i in [0, 1, 4, 5] {
        bitmap.set(i, true);
    }
    println!("Binary format: {bitmap}");
    println!("Debug format: {:?}", bitmap.iter().collect::<Vec<_>>());

    // Working with positions
    println!("\nPosition operations:");
    let mut bitmap = SmolBitmap::new();
    for i in [1, 3, 5, 7, 9] {
        bitmap.set(i, true);
    }

    println!("Bitmap: {:?}", bitmap.iter().collect::<Vec<_>>());
    println!("Position of bit 5 in set: {}", bitmap.position_of(5));
    println!("Position of bit 7 in set: {}", bitmap.position_of(7));
    println!("Number of set bits: {}", bitmap.len());
}
