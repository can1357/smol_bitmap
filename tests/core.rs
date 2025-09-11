use smol_bitmap::SmolBitmap;

#[test]
fn test_new() {
    let bitmap = SmolBitmap::new();
    assert_eq!(bitmap.capacity(), SmolBitmap::inline_capacity());
    assert!(!bitmap.is_spilled());
    assert!(bitmap.is_empty());
}

#[test]
fn test_basic_operations() {
    let mut bitmap = SmolBitmap::new();

    // Initially empty
    assert_eq!(bitmap.len(), 0);
    assert!(bitmap.is_empty());

    // Set some bits
    bitmap.insert(10);
    bitmap.insert(42);

    // Check the bits
    assert!(bitmap.get(10));
    assert!(bitmap.get(42));
    assert!(!bitmap.get(11));
    assert!(!bitmap.get(41));

    // Check length
    assert_eq!(bitmap.len(), 2);
    assert!(!bitmap.is_empty());
}

#[test]
fn test_spilled_storage() {
    let mut bitmap = SmolBitmap::new();
    assert!(!bitmap.is_spilled());

    // Set a bit beyond inline capacity
    bitmap.insert(200);
    assert!(bitmap.is_spilled());
    assert!(bitmap.get(200));
}

#[test]
fn test_iterators() {
    let mut bitmap = SmolBitmap::new();
    bitmap.insert(1);
    bitmap.insert(5);
    bitmap.insert(10);

    let bits: Vec<usize> = bitmap.iter().collect();
    assert_eq!(bits, vec![1, 5, 10]);

    // Test reverse iteration
    let rev_bits: Vec<usize> = bitmap.iter().rev().collect();
    assert_eq!(rev_bits, vec![10, 5, 1]);
}

#[test]
fn test_into_iterator() {
    let mut bitmap = SmolBitmap::new();
    bitmap.insert(2);
    bitmap.insert(7);

    let bits: Vec<usize> = bitmap.into_iter().collect();
    assert_eq!(bits, vec![2, 7]);
}

#[test]
fn test_from_iterator() {
    let bits = vec![1, 3, 5, 7];
    let bitmap: SmolBitmap = bits.into_iter().collect();

    assert!(bitmap.get(1));
    assert!(bitmap.get(3));
    assert!(bitmap.get(5));
    assert!(bitmap.get(7));
    assert!(!bitmap.get(2));
}

#[test]
fn test_extend() {
    let mut bitmap = SmolBitmap::new();
    bitmap.insert(1);

    bitmap.extend(vec![3, 5, 7]);

    assert!(bitmap.get(1));
    assert!(bitmap.get(3));
    assert!(bitmap.get(5));
    assert!(bitmap.get(7));
}

#[test]
fn test_union() {
    let mut a = SmolBitmap::new();
    let mut b = SmolBitmap::new();

    a.insert(1);
    a.insert(3);
    b.insert(2);
    b.insert(3);

    let union = a.union(&b);
    assert!(union.get(1));
    assert!(union.get(2));
    assert!(union.get(3));

    a.union_with(&b);
    assert!(a.get(1));
    assert!(a.get(2));
    assert!(a.get(3));
}

#[test]
fn test_intersection() {
    let mut a = SmolBitmap::new();
    let mut b = SmolBitmap::new();

    a.insert(1);
    a.insert(3);
    b.insert(2);
    b.insert(3);

    let intersection = a.intersection(&b);
    assert!(!intersection.get(1));
    assert!(!intersection.get(2));
    assert!(intersection.get(3));
}

#[test]
fn test_difference() {
    let mut a = SmolBitmap::new();
    let mut b = SmolBitmap::new();

    a.insert(1);
    a.insert(3);
    b.insert(2);
    b.insert(3);

    let difference = a.difference(&b);
    assert!(difference.get(1));
    assert!(!difference.get(2));
    assert!(!difference.get(3));
}

#[test]
fn test_symmetric_difference() {
    let mut a = SmolBitmap::new();
    let mut b = SmolBitmap::new();

    a.insert(1);
    a.insert(3);
    b.insert(2);
    b.insert(3);

    let sym_diff = a.symmetric_difference(&b);
    assert!(sym_diff.get(1));
    assert!(sym_diff.get(2));
    assert!(!sym_diff.get(3));
}

#[test]
fn test_subset_superset() {
    let mut a = SmolBitmap::new();
    let mut b = SmolBitmap::new();

    a.insert(1);
    a.insert(3);
    b.insert(1);

    assert!(b.is_subset(&a));
    assert!(a.is_superset(&b));
    assert!(!a.is_subset(&b));
    assert!(!b.is_superset(&a));
}

#[test]
fn test_disjoint() {
    let mut a = SmolBitmap::new();
    let mut b = SmolBitmap::new();

    a.insert(1);
    b.insert(2);
    assert!(a.is_disjoint(&b));

    b.insert(1);
    assert!(!a.is_disjoint(&b));
}

#[test]
fn test_select() {
    let mut bitmap = SmolBitmap::new();
    bitmap.insert(0);
    bitmap.insert(2);
    bitmap.insert(4);

    let items = ["a", "b", "c", "d", "e"];
    let selected: Vec<_> = bitmap.select(items.iter().copied()).collect();
    assert_eq!(selected, vec!["a", "c", "e"]);
}

#[test]
fn test_first_last() {
    let mut bitmap = SmolBitmap::new();
    assert_eq!(bitmap.first(), None);
    assert_eq!(bitmap.last(), None);

    bitmap.insert(10);
    bitmap.insert(5);
    bitmap.insert(20);

    assert_eq!(bitmap.first(), Some(5));
    assert_eq!(bitmap.last(), Some(20));
}

#[test]
fn test_rank() {
    let mut bitmap = SmolBitmap::new();
    bitmap.insert(5);
    bitmap.insert(10);
    bitmap.insert(15);
    bitmap.insert(20);

    assert_eq!(bitmap.rank(0), 0);
    assert_eq!(bitmap.rank(6), 1);
    assert_eq!(bitmap.rank(12), 2);
    assert_eq!(bitmap.rank(25), 4);
}

#[test]
fn test_count_ones_zeros() {
    let mut bitmap = SmolBitmap::new();
    bitmap.insert(5);
    bitmap.insert(10);

    assert_eq!(bitmap.count_ones(), 2);
    assert_eq!(bitmap.count_zeros(), bitmap.capacity() - 2);
}

#[test]
fn test_complement_range() {
    let mut bitmap = SmolBitmap::new();
    bitmap.insert(1);
    bitmap.insert(3);

    bitmap.complement_range(0, 5);
    assert!(bitmap.get(0));
    assert!(!bitmap.get(1));
    assert!(bitmap.get(2));
    assert!(!bitmap.get(3));
    assert!(bitmap.get(4));
}

#[test]
fn test_complement() {
    let mut bitmap = SmolBitmap::new();
    assert!(!bitmap.get(5));

    bitmap.complement(5);
    assert!(bitmap.get(5));

    bitmap.complement(5);
    assert!(!bitmap.get(5));
}

#[test]
fn test_next_prev_set_bit() {
    let mut bitmap = SmolBitmap::new();
    bitmap.insert(5);
    bitmap.insert(10);
    bitmap.insert(15);

    assert_eq!(bitmap.next_set_bit(0), Some(5));
    assert_eq!(bitmap.next_set_bit(6), Some(10));
    assert_eq!(bitmap.next_set_bit(16), None);

    assert_eq!(bitmap.prev_set_bit(20), Some(15));
    assert_eq!(bitmap.prev_set_bit(14), Some(10));
    assert_eq!(bitmap.prev_set_bit(4), None);
}

#[test]
fn test_retain() {
    let mut bitmap = SmolBitmap::new();
    bitmap.insert(1);
    bitmap.insert(2);
    bitmap.insert(5);
    bitmap.insert(8);

    bitmap.retain(|bit| bit.is_multiple_of(2));

    assert!(!bitmap.get(1));
    assert!(bitmap.get(2));
    assert!(!bitmap.get(5));
    assert!(bitmap.get(8));
}

#[test]
fn test_remove_prefix() {
    let mut bitmap = SmolBitmap::new();
    // Create pattern: 1111001010000...
    for i in 0..4 {
        bitmap.insert(i);
    }
    bitmap.insert(6);
    bitmap.insert(8);

    let removed = bitmap.remove_prefix(true);
    assert_eq!(removed, 4);

    // After removing 4 leading 1s, we should have: 001010000... shifted left to:
    // 1010000...
    assert!(!bitmap.get(0)); // was bit 4 (0)
    assert!(!bitmap.get(1)); // was bit 5 (0)
    assert!(bitmap.get(2)); // was bit 6 (1)
    assert!(!bitmap.get(3)); // was bit 7 (0)
    assert!(bitmap.get(4)); // was bit 8 (1)
}

#[test]
fn test_shrink_to_fit() {
    let mut bitmap = SmolBitmap::new();
    bitmap.insert(300);
    assert!(bitmap.is_spilled());

    bitmap.remove(300);
    bitmap.shrink_to_fit();
    // Should move back to inline storage since no bits are set
    assert!(!bitmap.is_spilled());
}

#[test]
fn test_with_capacity() {
    let bitmap = SmolBitmap::with_capacity(100);
    assert!(!bitmap.is_spilled());
    assert!(bitmap.capacity() >= 100);

    let bitmap = SmolBitmap::with_capacity(1000);
    assert!(bitmap.is_spilled());
    assert!(bitmap.capacity() >= 1000);
}

#[test]
fn test_reserve() {
    let mut bitmap = SmolBitmap::new();
    let original_capacity = bitmap.capacity();

    bitmap.reserve(300);
    assert!(bitmap.capacity() >= original_capacity + 300);
}

#[test]
fn test_clear() {
    let mut bitmap = SmolBitmap::new();
    bitmap.insert(10);
    bitmap.insert(200);

    assert!(bitmap.is_spilled());
    assert!(!bitmap.is_empty());

    bitmap.clear();
    assert!(bitmap.is_empty());
    assert_eq!(bitmap.len(), 0);
}

#[cfg(feature = "serde")]
mod serde_tests {
    use super::*;

    #[test]
    fn test_serde_json() {
        let mut bitmap = SmolBitmap::new();
        bitmap.insert(1);
        bitmap.insert(10);
        bitmap.insert(100);

        let json = serde_json::to_string(&bitmap).unwrap();
        let deserialized: SmolBitmap = serde_json::from_str(&json).unwrap();

        assert_eq!(
            bitmap.iter().collect::<Vec<_>>(),
            deserialized.iter().collect::<Vec<_>>()
        );
    }
}

#[test]
fn test_debug_format() {
    let mut bitmap = SmolBitmap::new();
    bitmap.insert(1);
    bitmap.insert(5);

    let debug_str = format!("{bitmap:?}");
    assert!(debug_str.contains('1'));
    assert!(debug_str.contains('5'));
}

#[test]
fn test_binary_format() {
    let mut bitmap = SmolBitmap::new();
    bitmap.insert(0);
    bitmap.insert(2);

    let binary_str = format!("{bitmap:b}");
    assert!(binary_str.contains("101")); // bits 2, 1, 0 => 101

    let binary_alt = format!("{bitmap:#b}");
    assert!(binary_alt.starts_with("0b"));
}

#[test]
fn test_from_str() {
    use core::str::FromStr;

    let bitmap = SmolBitmap::from_str("101").unwrap();
    assert!(bitmap.get(0));
    assert!(!bitmap.get(1));
    assert!(bitmap.get(2));

    let bitmap = SmolBitmap::from_str("0b1010").unwrap();
    assert!(!bitmap.get(0));
    assert!(bitmap.get(1));
    assert!(!bitmap.get(2));
    assert!(bitmap.get(3));

    // Test error cases
    assert!(SmolBitmap::from_str("").is_err());
    assert!(SmolBitmap::from_str("102").is_err()); // Invalid character
}

#[test]
fn test_find_first_zero_all_set() {
    let mut bitmap = SmolBitmap::new();
    // Set all bits up to inline capacity
    for i in 0..SmolBitmap::inline_capacity() {
        bitmap.insert(i);
    }
    assert_eq!(bitmap.find_first_zero(), None); // All bits set, should return None
}
