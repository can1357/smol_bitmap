use smol_bitmap::{SmolBitmap, bitmap};

#[test]
fn test_empty_bitmap() {
    let bmp = bitmap![];
    assert_eq!(bmp.capacity(), SmolBitmap::inline_capacity());
    assert_eq!(bmp.len(), 0);
    assert!(bmp.is_empty());
    assert!(!bmp.is_spilled());
}

#[test]
fn test_single_bit() {
    let bmp = bitmap![5];
    assert!(bmp.get(5));
    assert!(!bmp.get(0));
    assert!(!bmp.get(4));
    assert!(!bmp.get(6));
    assert_eq!(bmp.len(), 1);
    assert!(!bmp.is_spilled());
}

#[test]
fn test_multiple_bits_inline() {
    let bmp = bitmap![1, 5, 10, 20, 50, 100];

    // Check that all specified bits are set
    assert!(bmp.get(1));
    assert!(bmp.get(5));
    assert!(bmp.get(10));
    assert!(bmp.get(20));
    assert!(bmp.get(50));
    assert!(bmp.get(100));

    // Check that other bits are not set
    assert!(!bmp.get(0));
    assert!(!bmp.get(2));
    assert!(!bmp.get(15));
    assert!(!bmp.get(101));

    assert_eq!(bmp.len(), 6);
    assert!(!bmp.is_spilled()); // 100 < 127 (inline capacity)
}

#[test]
fn test_bits_requiring_heap_storage() {
    let bmp = bitmap![100, 200, 300, 500, 1000];

    // Check that all specified bits are set
    assert!(bmp.get(100));
    assert!(bmp.get(200));
    assert!(bmp.get(300));
    assert!(bmp.get(500));
    assert!(bmp.get(1000));

    // Check that other bits are not set
    assert!(!bmp.get(99));
    assert!(!bmp.get(101));
    assert!(!bmp.get(999));
    assert!(!bmp.get(1001));

    assert_eq!(bmp.len(), 5);
    assert!(bmp.is_spilled()); // 1000 > 127 (inline capacity)
}

#[test]
fn test_duplicate_bits() {
    // Duplicate bits should only be set once
    let bmp = bitmap![5, 5, 10, 10, 10, 20];
    assert_eq!(bmp.len(), 3); // Only 3 unique bits
    assert!(bmp.get(5));
    assert!(bmp.get(10));
    assert!(bmp.get(20));
}

#[test]
fn test_unordered_bits() {
    // Bits don't need to be in order
    let bmp = bitmap![50, 10, 30, 5, 100, 1];
    assert!(bmp.get(1));
    assert!(bmp.get(5));
    assert!(bmp.get(10));
    assert!(bmp.get(30));
    assert!(bmp.get(50));
    assert!(bmp.get(100));
    assert_eq!(bmp.len(), 6);
}

#[test]
fn test_trailing_comma() {
    // Should handle trailing comma correctly
    let bmp = bitmap![1, 2, 3,];
    assert!(bmp.get(1));
    assert!(bmp.get(2));
    assert!(bmp.get(3));
    assert_eq!(bmp.len(), 3);
}

#[test]
fn test_zero_bit() {
    // Should handle bit 0 correctly
    let bmp = bitmap![0];
    assert!(bmp.get(0));
    assert!(!bmp.get(1));
    assert_eq!(bmp.len(), 1);
}

#[test]
fn test_capacity_calculation() {
    // Test that capacity is correctly calculated as max_bit + 1
    let bmp1 = bitmap![10];
    assert!(bmp1.capacity() >= 11); // Should have capacity for at least bits 0-10

    let bmp2 = bitmap![0, 50, 100];
    assert!(bmp2.capacity() >= 101); // Should have capacity for at least bits 0-100

    let bmp3 = bitmap![500];
    assert!(bmp3.capacity() >= 501); // Should have capacity for at least bits 0-500
}

#[test]
fn test_comparison_with_manual_construction() {
    // bitmap! macro should produce same result as manual construction
    let macro_bmp = bitmap![5, 10, 15, 20];

    let mut manual_bmp = SmolBitmap::with_capacity(21);
    manual_bmp.insert(5);
    manual_bmp.insert(10);
    manual_bmp.insert(15);
    manual_bmp.insert(20);

    // Both should have the same bits set
    for i in 0..30 {
        assert_eq!(macro_bmp.get(i), manual_bmp.get(i), "Bit {i} differs");
    }

    assert_eq!(macro_bmp.len(), manual_bmp.len());
}

#[test]
fn test_large_bit_positions() {
    // Test with very large bit positions
    let bmp = bitmap![10000, 20000, 30000];
    assert!(bmp.get(10000));
    assert!(bmp.get(20000));
    assert!(bmp.get(30000));
    assert!(!bmp.get(9999));
    assert!(!bmp.get(30001));
    assert_eq!(bmp.len(), 3);
    assert!(bmp.is_spilled());
}

#[test]
fn test_expressions_in_macro() {
    // Test that expressions work in the macro
    const BIT1: usize = 10;
    const BIT2: usize = 20;

    let bmp = bitmap![BIT1, BIT2, 5 + 5, 2 * 15];
    assert!(bmp.get(10)); // BIT1
    assert!(bmp.get(20)); // BIT2
    assert!(bmp.get(10)); // 5 + 5
    assert!(bmp.get(30)); // 2 * 15
    assert_eq!(bmp.len(), 3); // 10, 20, 30 (note: 5+5 = 10, which is duplicate)
}
