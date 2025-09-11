use smol_bitmap::SmolBitmap;

#[test]
fn test_resize_expand() {
    let mut bitmap = SmolBitmap::new();
    bitmap.insert(50);
    bitmap.insert(100);

    // Expand within inline capacity
    bitmap.resize(120);
    assert_eq!(bitmap.capacity(), 127); // Still inline
    assert!(bitmap.get(50));
    assert!(bitmap.get(100));
    assert!(!bitmap.get(110)); // New bits are zero
    assert!(!bitmap.is_spilled());

    // Expand beyond inline capacity
    bitmap.resize(200);
    assert!(bitmap.is_spilled());
    assert!(bitmap.capacity() >= 200);
    assert!(bitmap.get(50));
    assert!(bitmap.get(100));
    assert!(!bitmap.get(150)); // New bits are zero
}

#[test]
fn test_resize_shrink() {
    let mut bitmap = SmolBitmap::new();
    bitmap.insert(50);
    bitmap.insert(100);
    bitmap.insert(150);

    // Force spill first
    bitmap.insert(200);
    assert!(bitmap.is_spilled());

    // Resize to 120 bits - should clear bits beyond 120
    bitmap.resize(120);
    assert!(bitmap.get(50));
    assert!(bitmap.get(100));
    assert!(!bitmap.get(150)); // Cleared
    assert!(!bitmap.get(200)); // Cleared

    // Resize to fit in inline storage
    bitmap.resize(100);
    assert!(bitmap.get(50));
    assert!(!bitmap.get(100)); // Cleared
    bitmap.shrink_to_fit();
    assert!(!bitmap.is_spilled()); // Should be back to inline
}

#[test]
fn test_resize_no_op() {
    let mut bitmap = SmolBitmap::new();
    bitmap.insert(50);

    let initial_capacity = bitmap.capacity();
    bitmap.resize(initial_capacity);

    // Should be unchanged
    assert_eq!(bitmap.capacity(), initial_capacity);
    assert!(bitmap.get(50));
}

#[test]
fn test_truncate_basic() {
    let mut bitmap = SmolBitmap::new();
    bitmap.insert(50);
    bitmap.insert(100);
    bitmap.insert(150);

    // Truncate to 120 bits
    bitmap.truncate(120);
    assert!(bitmap.get(50));
    assert!(bitmap.get(100));
    assert!(!bitmap.get(150)); // Cleared

    // Further truncation
    bitmap.truncate(60);
    assert!(bitmap.get(50));
    assert!(!bitmap.get(100)); // Cleared
}

#[test]
fn test_truncate_to_zero() {
    let mut bitmap = SmolBitmap::new();
    bitmap.insert(50);
    bitmap.insert(100);

    bitmap.truncate(0);
    assert!(bitmap.is_empty());
    assert!(!bitmap.get(50));
    assert!(!bitmap.get(100));
}

#[test]
fn test_truncate_partial_word() {
    let mut bitmap = SmolBitmap::new();

    // Set bits across word boundary
    for i in 60..70 {
        bitmap.insert(i);
    }

    // Truncate to 65 bits - should clear bits 65-69
    bitmap.truncate(65);
    for i in 60..65 {
        assert!(bitmap.get(i), "Bit {i} should be set");
    }
    for i in 65..70 {
        assert!(!bitmap.get(i), "Bit {i} should be cleared");
    }
}

#[test]
fn test_truncate_shrink_to_inline() {
    let mut bitmap = SmolBitmap::new();

    // Force spill by setting high bits
    bitmap.insert(200);
    bitmap.insert(50);
    assert!(bitmap.is_spilled());

    // Truncate to fit in inline storage
    bitmap.truncate(100);
    bitmap.shrink_to_fit();
    assert!(!bitmap.is_spilled()); // Should be back to inline
    assert!(bitmap.get(50));
    assert!(!bitmap.get(200));
}

#[test]
fn test_resize_preserves_bits() {
    let mut bitmap = SmolBitmap::new();

    // Set a pattern
    for i in (0..100).step_by(3) {
        bitmap.insert(i);
    }

    // Expand
    bitmap.resize(150);

    // Original bits should be preserved
    for i in 0..100 {
        assert_eq!(bitmap.get(i), i.is_multiple_of(3));
    }

    // New bits should be zero
    for i in 100..150 {
        assert!(!bitmap.get(i));
    }

    // Shrink
    bitmap.resize(50);

    // Remaining bits should still be preserved
    for i in 0..50 {
        assert_eq!(bitmap.get(i), i.is_multiple_of(3));
    }
}

#[test]
fn test_truncate_bit_127() {
    let mut bitmap = SmolBitmap::new();

    // Set bit 127 (which forces spill)
    bitmap.insert(127);
    assert!(bitmap.is_spilled());

    // Truncate to 127 bits - bit 126 is the highest keepable bit
    bitmap.truncate(127);
    bitmap.shrink_to_fit();
    assert!(!bitmap.get(127)); // Should be cleared
    assert!(!bitmap.is_spilled()); // Should be back to inline
}

#[test]
fn test_resize_then_set() {
    let mut bitmap = SmolBitmap::new();

    // Resize to specific size
    bitmap.resize(100);

    // Should be able to set bits up to that size
    bitmap.insert(99);
    assert!(bitmap.get(99));

    // Setting beyond should still work (extends capacity)
    bitmap.insert(150);
    assert!(bitmap.get(150));
}
