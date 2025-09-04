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
    bitmap.set(10, true);
    bitmap.set(42, true);

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
    bitmap.set(200, true);
    assert!(bitmap.is_spilled());
    assert!(bitmap.get(200));
}

#[test]
fn test_iterators() {
    let mut bitmap = SmolBitmap::new();
    bitmap.set(1, true);
    bitmap.set(5, true);
    bitmap.set(10, true);

    let bits: Vec<usize> = bitmap.iter().collect();
    assert_eq!(bits, vec![1, 5, 10]);

    // Test reverse iteration
    let rev_bits: Vec<usize> = bitmap.iter().rev().collect();
    assert_eq!(rev_bits, vec![10, 5, 1]);
}

#[test]
fn test_into_iterator() {
    let mut bitmap = SmolBitmap::new();
    bitmap.set(2, true);
    bitmap.set(7, true);

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
    bitmap.set(1, true);

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

    a.set(1, true);
    a.set(3, true);
    b.set(2, true);
    b.set(3, true);

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

    a.set(1, true);
    a.set(3, true);
    b.set(2, true);
    b.set(3, true);

    let intersection = a.intersection(&b);
    assert!(!intersection.get(1));
    assert!(!intersection.get(2));
    assert!(intersection.get(3));
}

#[test]
fn test_difference() {
    let mut a = SmolBitmap::new();
    let mut b = SmolBitmap::new();

    a.set(1, true);
    a.set(3, true);
    b.set(2, true);
    b.set(3, true);

    let difference = a.difference(&b);
    assert!(difference.get(1));
    assert!(!difference.get(2));
    assert!(!difference.get(3));
}

#[test]
fn test_symmetric_difference() {
    let mut a = SmolBitmap::new();
    let mut b = SmolBitmap::new();

    a.set(1, true);
    a.set(3, true);
    b.set(2, true);
    b.set(3, true);

    let sym_diff = a.symmetric_difference(&b);
    assert!(sym_diff.get(1));
    assert!(sym_diff.get(2));
    assert!(!sym_diff.get(3));
}

#[test]
fn test_subset_superset() {
    let mut a = SmolBitmap::new();
    let mut b = SmolBitmap::new();

    a.set(1, true);
    a.set(3, true);
    b.set(1, true);

    assert!(b.is_subset(&a));
    assert!(a.is_superset(&b));
    assert!(!a.is_subset(&b));
    assert!(!b.is_superset(&a));
}

#[test]
fn test_disjoint() {
    let mut a = SmolBitmap::new();
    let mut b = SmolBitmap::new();

    a.set(1, true);
    b.set(2, true);
    assert!(a.is_disjoint(&b));

    b.set(1, true);
    assert!(!a.is_disjoint(&b));
}

#[test]
fn test_select() {
    let mut bitmap = SmolBitmap::new();
    bitmap.set(0, true);
    bitmap.set(2, true);
    bitmap.set(4, true);

    let items = ["a", "b", "c", "d", "e"];
    let selected: Vec<_> = bitmap.select(items.iter().copied()).collect();
    assert_eq!(selected, vec!["a", "c", "e"]);
}

#[test]
fn test_first_last() {
    let mut bitmap = SmolBitmap::new();
    assert_eq!(bitmap.first(), None);
    assert_eq!(bitmap.last(), None);

    bitmap.set(10, true);
    bitmap.set(5, true);
    bitmap.set(20, true);

    assert_eq!(bitmap.first(), Some(5));
    assert_eq!(bitmap.last(), Some(20));
}

#[test]
fn test_position_of() {
    let mut bitmap = SmolBitmap::new();
    bitmap.set(5, true);
    bitmap.set(10, true);
    bitmap.set(15, true);
    bitmap.set(20, true);

    assert_eq!(bitmap.position_of(0), 0);
    assert_eq!(bitmap.position_of(6), 1);
    assert_eq!(bitmap.position_of(12), 2);
    assert_eq!(bitmap.position_of(25), 4);
}

#[test]
fn test_count_ones_zeros() {
    let mut bitmap = SmolBitmap::new();
    bitmap.set(5, true);
    bitmap.set(10, true);

    assert_eq!(bitmap.count_ones(), 2);
    assert_eq!(bitmap.count_zeros(), bitmap.capacity() - 2);
}

#[test]
fn test_complement() {
    let mut bitmap = SmolBitmap::new();
    bitmap.set(1, true);
    bitmap.set(3, true);

    let complement = bitmap.complement(4);
    assert!(complement.get(0));
    assert!(!complement.get(1));
    assert!(complement.get(2));
    assert!(!complement.get(3));
    assert!(complement.get(4));
}

#[test]
fn test_toggle() {
    let mut bitmap = SmolBitmap::new();
    assert!(!bitmap.get(5));

    bitmap.toggle(5);
    assert!(bitmap.get(5));

    bitmap.toggle(5);
    assert!(!bitmap.get(5));
}

#[test]
fn test_next_prev_set_bit() {
    let mut bitmap = SmolBitmap::new();
    bitmap.set(5, true);
    bitmap.set(10, true);
    bitmap.set(15, true);

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
    bitmap.set(1, true);
    bitmap.set(2, true);
    bitmap.set(5, true);
    bitmap.set(8, true);

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
        bitmap.set(i, true);
    }
    bitmap.set(6, true);
    bitmap.set(8, true);

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
    bitmap.set(300, true);
    assert!(bitmap.is_spilled());

    bitmap.set(300, false);
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
    bitmap.set(10, true);
    bitmap.set(200, true);

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
        bitmap.set(1, true);
        bitmap.set(10, true);
        bitmap.set(100, true);

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
    bitmap.set(1, true);
    bitmap.set(5, true);

    let debug_str = format!("{bitmap:?}");
    assert!(debug_str.contains("1"));
    assert!(debug_str.contains("5"));
}

#[test]
fn test_binary_format() {
    let mut bitmap = SmolBitmap::new();
    bitmap.set(0, true);
    bitmap.set(2, true);

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
        bitmap.set(i, true);
    }
    assert_eq!(bitmap.find_first_zero(), None); // All bits set, should return None
}
