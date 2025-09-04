use smol_bitmap::{SmolBitmap, TryFromBitmapError};
use std::{collections::BTreeSet, convert::TryFrom};

#[test]
fn test_inline_storage() {
    let mut mask = SmolBitmap::new();

    // Test inline storage capacity
    for i in 0..SmolBitmap::inline_capacity() {
        assert!(!mask.get(i));
        mask.set(i, true);
        assert!(mask.get(i));
    }
}

#[test]
fn test_reserve_transitions_to_external() {
    let mut bitmap = SmolBitmap::new();
    assert!(!bitmap.is_spilled());
    assert_eq!(bitmap.capacity(), SmolBitmap::inline_capacity());

    // Reserve enough space for 300 bits
    bitmap.reserve(300);

    // Should have transitioned to external storage
    assert!(
        bitmap.is_spilled(),
        "Should have spilled to external storage"
    );
    assert!(bitmap.capacity() >= 300, "Capacity should be at least 300");

    // Should be able to set bits beyond inline capacity
    bitmap.set(200, true);
    assert!(bitmap.get(200));
}

#[test]
fn test_highest_inline_bit_forces_external() {
    let mut bitmap = SmolBitmap::new();
    let highest_inline_bit = SmolBitmap::inline_capacity();

    // Set the bit at inline capacity (which is beyond inline storage)
    bitmap.set(highest_inline_bit, true);

    // This should force external storage because it's beyond inline capacity
    assert!(
        bitmap.is_spilled(),
        "Setting bit at inline capacity should force external storage"
    );
    assert!(bitmap.get(highest_inline_bit));
}

#[test]
fn test_external_storage() {
    let mut mask = SmolBitmap::new();

    // Force external storage
    let inline_cap = SmolBitmap::inline_capacity();
    mask.set(inline_cap, true);
    assert!(mask.is_spilled());
    assert!(mask.get(inline_cap));

    // Test that other bits are still false
    for i in 0..inline_cap {
        assert!(!mask.get(i));
    }
}

#[test]
fn test_union_intersection_difference() {
    let mut a = SmolBitmap::new();
    let mut b = SmolBitmap::new();

    a.set(10, true);
    a.set(20, true);
    a.set(30, true);
    b.set(20, true);
    b.set(30, true);
    b.set(40, true);

    // Union: {10, 20, 30, 40}
    let union = a.union(&b);
    assert!(union.get(10));
    assert!(union.get(20));
    assert!(union.get(30));
    assert!(union.get(40));

    // Intersection: {20, 30}
    let intersection = a.intersection(&b);
    assert!(!intersection.get(10));
    assert!(intersection.get(20));
    assert!(intersection.get(30));
    assert!(!intersection.get(40));

    // Difference (a - b): {10}
    let difference = a.difference(&b);
    assert!(difference.get(10));
    assert!(!difference.get(20));
    assert!(!difference.get(30));
    assert!(!difference.get(40));

    // Symmetric difference: {10, 40}
    let sym_diff = a.symmetric_difference(&b);
    assert!(sym_diff.get(10));
    assert!(!sym_diff.get(20));
    assert!(!sym_diff.get(30));
    assert!(sym_diff.get(40));
}

#[test]
fn test_iter_forward_backward() {
    let mut bitmap = SmolBitmap::new();
    bitmap.set(0, true);
    bitmap.set(10, true);
    bitmap.set(63, true);
    bitmap.set(64, true);
    bitmap.set(100, true);
    bitmap.set(200, true);

    // Forward iteration
    let collected: Vec<_> = bitmap.iter().collect();
    assert_eq!(collected, vec![0, 10, 63, 64, 100, 200]);

    // Backward iteration
    let collected_rev: Vec<_> = bitmap.iter().rev().collect();
    assert_eq!(collected_rev, vec![200, 100, 64, 63, 10, 0]);
}

#[test]
fn test_from_and_into_iter() {
    let bits = vec![5, 15, 25, 100, 200];
    let bitmap: SmolBitmap = bits.iter().copied().collect();

    for &bit in &bits {
        assert!(bitmap.get(bit));
    }

    // Check some bits that weren't set
    assert!(!bitmap.get(0));
    assert!(!bitmap.get(10));
    assert!(!bitmap.get(50));

    // Test into_iter
    let collected: Vec<_> = bitmap.into_iter().collect();
    assert_eq!(collected, bits);
}

#[test]
fn test_eq_and_ord() {
    let mut a = SmolBitmap::new();
    let mut b = SmolBitmap::new();

    assert_eq!(a, b);

    a.set(10, true);
    assert_ne!(a, b);
    assert!(a > b); // Non-empty > empty

    b.set(10, true);
    assert_eq!(a, b);

    b.set(20, true);
    assert!(a < b); // {10} < {10, 20}
}

#[test]
fn test_shrink_to_fit() {
    let mut bitmap = SmolBitmap::new();

    // Set a high bit then clear it
    bitmap.set(300, true);
    assert!(bitmap.is_spilled());
    bitmap.set(300, false);

    // Set a low bit
    bitmap.set(50, true);

    bitmap.shrink_to_fit();
    // Should potentially move back to inline if possible
    assert!(bitmap.get(50));
    assert!(!bitmap.get(300));
}

#[test]
fn test_exact_size_iterator() {
    let mut bitmap = SmolBitmap::new();
    for i in (0..300).step_by(2) {
        bitmap.set(i, true);
    }

    let iter = bitmap.iter();
    assert_eq!(iter.len(), 150);
    assert_eq!(iter.count(), 150);
}

#[test]
fn test_retain() {
    let mut bitmap = SmolBitmap::new();
    bitmap.set(1, true);
    bitmap.set(2, true);
    bitmap.set(5, true);
    bitmap.set(8, true);
    bitmap.set(10, true);
    bitmap.set(15, true);

    // Retain only even indices
    bitmap.retain(|bit| bit.is_multiple_of(2));

    assert!(!bitmap.get(1));
    assert!(bitmap.get(2));
    assert!(!bitmap.get(5));
    assert!(bitmap.get(8));
    assert!(bitmap.get(10));
    assert!(!bitmap.get(15));
}

#[cfg(feature = "serde")]
#[test]
fn test_serialization() {
    use serde_json;

    let mut bitmap = SmolBitmap::new();
    bitmap.set(5, true);
    bitmap.set(100, true);
    bitmap.set(200, true);

    // JSON serialization
    let json = serde_json::to_string(&bitmap).expect("Should serialize to JSON");
    let deserialized: SmolBitmap =
        serde_json::from_str(&json).expect("Should deserialize from JSON");
    assert_eq!(bitmap, deserialized);

    // Test empty bitmap
    let empty = SmolBitmap::new();
    let json = serde_json::to_string(&empty).expect("Should serialize empty bitmap");
    let deserialized: SmolBitmap =
        serde_json::from_str(&json).expect("Should deserialize empty bitmap");
    assert_eq!(empty, deserialized);
}

#[test]
fn test_parse_from_string() {
    // Binary notation
    let bitmap: SmolBitmap = "0b1010".parse().expect("Should parse binary");
    assert!(bitmap.get(1));
    assert!(!bitmap.get(0));
    assert!(bitmap.get(3));
    assert!(!bitmap.get(2));

    // Binary notation with multiple bits
    let bitmap: SmolBitmap = "0b1111".parse().expect("Should parse binary");
    assert!(bitmap.get(0));
    assert!(bitmap.get(1));
    assert!(bitmap.get(2));
    assert!(bitmap.get(3));
    assert!(!bitmap.get(4));

    // Invalid formats
    assert!("invalid".parse::<SmolBitmap>().is_err());
    assert!("0b2".parse::<SmolBitmap>().is_err());
}

// Proptest-based property tests
#[cfg(test)]
mod property_tests {
    use super::*;
    use proptest::prelude::*;

    prop_compose! {
        fn arb_bit_indices()(
            indices in prop::collection::btree_set(0usize..1000, 0..100)
        ) -> BTreeSet<usize> {
            indices
        }
    }

    proptest! {
        #[test]
        fn prop_iter_matches_set(indices in arb_bit_indices()) {
            let mut bitmap = SmolBitmap::new();
            for &idx in &indices {
                bitmap.set(idx, true);
            }

            let collected: BTreeSet<usize> = bitmap.iter().collect();
            prop_assert_eq!(collected, indices);
        }

        #[test]
        fn prop_union_commutative(
            indices_a in arb_bit_indices(),
            indices_b in arb_bit_indices()
        ) {
            let mut a = SmolBitmap::new();
            let mut b = SmolBitmap::new();

            for &idx in &indices_a {
                a.set(idx, true);
            }
            for &idx in &indices_b {
                b.set(idx, true);
            }

            let union_ab = a.union(&b);
            let union_ba = b.union(&a);

            prop_assert_eq!(union_ab, union_ba);
        }

        #[test]
        fn prop_intersection_commutative(
            indices_a in arb_bit_indices(),
            indices_b in arb_bit_indices()
        ) {
            let mut a = SmolBitmap::new();
            let mut b = SmolBitmap::new();

            for &idx in &indices_a {
                a.set(idx, true);
            }
            for &idx in &indices_b {
                b.set(idx, true);
            }

            let inter_ab = a.intersection(&b);
            let inter_ba = b.intersection(&a);

            prop_assert_eq!(inter_ab, inter_ba);
        }

    }
}

// ============================================================================
// Tests for New Bitwise Operators
// ============================================================================

#[test]
fn test_bitwise_operators() {
    let mut a = SmolBitmap::new();
    a.set(0, true);
    a.set(1, true);
    a.set(3, true);

    let mut b = SmolBitmap::new();
    b.set(1, true);
    b.set(2, true);
    b.set(3, true);

    // Test BitAnd (&)
    let and_result = &a & &b;
    assert!(!and_result.get(0)); // Only in a
    assert!(and_result.get(1)); // In both
    assert!(!and_result.get(2)); // Only in b
    assert!(and_result.get(3)); // In both

    // Test BitOr (|)
    let or_result = &a | &b;
    assert!(or_result.get(0)); // From a
    assert!(or_result.get(1)); // In both
    assert!(or_result.get(2)); // From b
    assert!(or_result.get(3)); // In both

    // Test BitXor (^)
    let xor_result = &a ^ &b;
    assert!(xor_result.get(0)); // Only in a
    assert!(!xor_result.get(1)); // In both, so not in XOR
    assert!(xor_result.get(2)); // Only in b
    assert!(!xor_result.get(3)); // In both, so not in XOR
}

#[test]
fn test_bitwise_assign_operators() {
    // Test BitAndAssign (&=)
    let mut a = SmolBitmap::new();
    a.set(0, true);
    a.set(1, true);
    a.set(3, true);

    let mut b = SmolBitmap::new();
    b.set(1, true);
    b.set(2, true);
    b.set(3, true);

    a &= &b;
    assert!(!a.get(0)); // Was only in a, removed
    assert!(a.get(1)); // In both, kept
    assert!(!a.get(2)); // Not in a
    assert!(a.get(3)); // In both, kept

    // Test BitOrAssign (|=)
    let mut c = SmolBitmap::new();
    c.set(0, true);
    c.set(1, true);

    let mut d = SmolBitmap::new();
    d.set(2, true);
    d.set(3, true);

    c |= &d;
    assert!(c.get(0));
    assert!(c.get(1));
    assert!(c.get(2));
    assert!(c.get(3));

    // Test BitXorAssign (^=)
    let mut e = SmolBitmap::new();
    e.set(0, true);
    e.set(1, true);
    e.set(3, true);

    let mut f = SmolBitmap::new();
    f.set(1, true);
    f.set(2, true);
    f.set(3, true);

    e ^= &f;
    assert!(e.get(0)); // Only in original e
    assert!(!e.get(1)); // In both, removed
    assert!(e.get(2)); // Only in f, added
    assert!(!e.get(3)); // In both, removed
}

#[test]
fn test_not_operator() {
    let mut a = SmolBitmap::new();
    a.set(0, true);
    a.set(2, true);
    a.set(4, true);

    let b = !&a;
    assert!(!b.get(0)); // Was set, now unset
    assert!(b.get(1)); // Was unset, now set
    assert!(!b.get(2)); // Was set, now unset
    assert!(b.get(3)); // Was unset, now set
    assert!(!b.get(4)); // Was set, now unset

    // Test empty bitmap
    let empty = SmolBitmap::new();
    let not_empty = !&empty;
    assert!(not_empty.is_empty()); // Empty bitmap inverted is still empty
}

#[test]
fn test_bitwise_operators_spilled() {
    // Test with spilled storage (>127 bits)
    let mut a = SmolBitmap::new();
    a.set(150, true);
    a.set(200, true);
    a.set(250, true);

    let mut b = SmolBitmap::new();
    b.set(200, true);
    b.set(250, true);
    b.set(300, true);

    let and_result = &a & &b;
    assert!(!and_result.get(150));
    assert!(and_result.get(200));
    assert!(and_result.get(250));
    assert!(!and_result.get(300));

    let or_result = &a | &b;
    assert!(or_result.get(150));
    assert!(or_result.get(200));
    assert!(or_result.get(250));
    assert!(or_result.get(300));

    let xor_result = &a ^ &b;
    assert!(xor_result.get(150));
    assert!(!xor_result.get(200));
    assert!(!xor_result.get(250));
    assert!(xor_result.get(300));
}

// ============================================================================
// Tests for Shift Operations
// ============================================================================

#[test]
fn test_shift_left() {
    let mut bitmap = SmolBitmap::new();
    bitmap.set(0, true);
    bitmap.set(1, true);
    bitmap.set(2, true);

    let shifted = bitmap.shl(3);
    assert!(!shifted.get(0));
    assert!(!shifted.get(1));
    assert!(!shifted.get(2));
    assert!(shifted.get(3));
    assert!(shifted.get(4));
    assert!(shifted.get(5));

    // Test zero shift
    let zero_shift = bitmap.shl(0);
    assert_eq!(zero_shift, bitmap);
}

#[test]
fn test_shift_right() {
    let mut bitmap = SmolBitmap::new();
    bitmap.set(3, true);
    bitmap.set(4, true);
    bitmap.set(5, true);

    let shifted = bitmap.shr(3);
    assert!(shifted.get(0));
    assert!(shifted.get(1));
    assert!(shifted.get(2));
    assert!(!shifted.get(3));

    // Test shifting below zero
    let shifted2 = bitmap.shr(4);
    assert!(shifted2.get(0)); // bit 4 -> 0
    assert!(shifted2.get(1)); // bit 5 -> 1
    assert!(!shifted2.get(2)); // no more bits
}

#[test]
fn test_shift_operations_spilled() {
    // Test with spilled storage
    let mut bitmap = SmolBitmap::new();
    bitmap.set(150, true);
    bitmap.set(200, true);

    let shifted_left = bitmap.shl(50);
    assert!(shifted_left.get(200));
    assert!(shifted_left.get(250));

    let shifted_right = bitmap.shr(50);
    assert!(shifted_right.get(100));
    assert!(shifted_right.get(150));
}

// ============================================================================
// Tests for Convenience Methods
// ============================================================================

#[test]
fn test_any_all_none() {
    let mut bitmap = SmolBitmap::new();

    // Empty bitmap
    assert!(!bitmap.any());
    assert!(bitmap.all()); // Empty bitmap returns true for all()
    assert!(bitmap.none());

    // Single bit
    bitmap.set(5, true);
    assert!(bitmap.any());
    assert!(!bitmap.all()); // Not all bits from 0-5 are set
    assert!(!bitmap.none());

    // Multiple consecutive bits
    bitmap.set(0, true);
    bitmap.set(1, true);
    bitmap.set(2, true);
    bitmap.set(3, true);
    bitmap.set(4, true);
    assert!(bitmap.any());
    assert!(bitmap.all()); // All bits 0-5 are set
    assert!(!bitmap.none());

    // Gap in bits
    bitmap.set(7, true);
    assert!(bitmap.any());
    assert!(!bitmap.all()); // Bit 6 is not set
    assert!(!bitmap.none());
}

#[test]
fn test_leading_trailing_zeros() {
    let mut bitmap = SmolBitmap::new();

    // Empty bitmap
    assert_eq!(bitmap.leading_zeros(), None);
    assert_eq!(bitmap.trailing_zeros(), None);

    // Single bit at position 5
    bitmap.set(5, true);
    assert_eq!(bitmap.leading_zeros(), Some(5)); // 5 leading zeros (bits 0-4)
    assert_eq!(bitmap.trailing_zeros(), Some(5)); // 5 trailing zeros from bit 5 down to bit 0

    // Add bit at position 0
    bitmap.set(0, true);
    assert_eq!(bitmap.leading_zeros(), Some(0)); // No leading zeros
    assert_eq!(bitmap.trailing_zeros(), Some(4)); // 4 trailing zeros from bit 5 down to bit 1 (bit 0 is set)

    // Add bit at position 10, leaving gap
    bitmap.set(10, true);
    assert_eq!(bitmap.leading_zeros(), Some(0)); // Still no leading zeros
    // Trailing zeros checks from bit 10 down - bits 9,8,7,6 are unset
    assert_eq!(bitmap.trailing_zeros(), Some(4)); // 4 trailing zeros from bit
    // 10 down to bit 5
}

#[test]
fn test_leading_trailing_ones() {
    let mut bitmap = SmolBitmap::new();

    // Empty bitmap
    assert_eq!(bitmap.leading_ones(), 0);
    assert_eq!(bitmap.trailing_ones(), 0);

    // Consecutive ones from bit 0
    bitmap.set(0, true);
    bitmap.set(1, true);
    bitmap.set(2, true);
    assert_eq!(bitmap.leading_ones(), 3);
    assert_eq!(bitmap.trailing_ones(), 3);

    // Add gap and more bits
    bitmap.set(5, true);
    bitmap.set(6, true);
    bitmap.set(7, true);
    assert_eq!(bitmap.leading_ones(), 3); // Still 3 (stops at bit 3)
    assert_eq!(bitmap.trailing_ones(), 3); // 3 consecutive from bit 7 down to 5
}

// ============================================================================
// Tests for Range Operations
// ============================================================================

#[test]
fn test_get_range() {
    let mut bitmap = SmolBitmap::new();
    bitmap.set(0, true);
    bitmap.set(2, true);
    bitmap.set(3, true);
    bitmap.set(5, true);

    // Extract bits 0-4: 101101 in positions -> 0b00101101
    assert_eq!(bitmap.get_range(0, 6), 0b101101);

    // Extract bits 2-5: bits at positions 2,3,4 -> 110
    assert_eq!(bitmap.get_range(2, 5), 0b011);

    // Extract empty range
    assert_eq!(bitmap.get_range(10, 10), 0);

    // Test maximum 64 bits
    let mut large = SmolBitmap::new();
    for i in 0usize..100 {
        if i.is_multiple_of(2) {
            large.set(i, true);
        }
    }
    // Should only extract first 64 bits
    let extracted = large.get_range(0, 100);
    assert_eq!(extracted.count_ones(), 32); // Every other bit for 64 bits
}

#[test]
#[should_panic(expected = "start must be <= end")]
fn test_get_range_panic() {
    let bitmap = SmolBitmap::new();
    _ = bitmap.get_range(10, 5); // start > end
}

// ============================================================================
// Additional Tests for New Features
// ============================================================================

#[test]
fn test_index_trait() {
    use std::ops::Index;

    let mut bitmap = SmolBitmap::new();
    bitmap.set(5, true);
    bitmap.set(10, true);

    // Test Index<usize>
    assert!(*bitmap.index(5));
    assert!(*bitmap.index(10));
    assert!(!(*bitmap.index(0)));
    assert!(!(*bitmap.index(6)));

    // Test with spilled storage
    bitmap.set(200, true);
    assert!(*bitmap.index(200));
    assert!(!(*bitmap.index(199)));
}

#[test]
fn test_index_no_panic() {
    use std::ops::Index;

    let bitmap = SmolBitmap::new();
    // Index trait now returns false for out-of-bounds, consistent with get()
    assert!(!(*bitmap.index(1000))); // Beyond capacity returns false
    assert!(!(*bitmap.index(0))); // Unset bit returns false

    let mut bitmap = SmolBitmap::new();
    bitmap.set(5, true);
    assert!(*bitmap.index(5)); // Set bit returns true
}

#[test]
fn test_find_zero_methods() {
    let mut bitmap = SmolBitmap::new();

    // Empty bitmap - all zeros
    assert_eq!(bitmap.find_first_zero(), Some(0));
    assert_eq!(bitmap.find_last_zero(), Some(0));

    // Set some bits
    bitmap.set(0, true);
    bitmap.set(1, true);
    bitmap.set(3, true);
    bitmap.set(5, true);

    assert_eq!(bitmap.find_first_zero(), Some(2));
    assert_eq!(bitmap.find_last_zero(), Some(4));

    assert_eq!(bitmap.find_next_zero(0), Some(2));
    assert_eq!(bitmap.find_next_zero(2), Some(2));
    assert_eq!(bitmap.find_next_zero(3), Some(4));

    assert_eq!(bitmap.find_prev_zero(5), Some(4));
    assert_eq!(bitmap.find_prev_zero(3), Some(2));
    assert_eq!(bitmap.find_prev_zero(1), None); // Bit 0 and 1 are set, no zeros at or before

    // Test with spilled storage
    let mut large = SmolBitmap::new();
    for i in 0..200 {
        large.set(i, true);
    }
    assert_eq!(large.find_first_zero(), Some(200));

    large.set(150, false);
    assert_eq!(large.find_first_zero(), Some(150));
}

#[test]
fn test_count_range_methods() {
    let mut bitmap = SmolBitmap::new();
    bitmap.set(1, true);
    bitmap.set(3, true);
    bitmap.set(5, true);
    bitmap.set(7, true);
    bitmap.set(9, true);

    assert_eq!(bitmap.count_ones_range(0, 10), 5);
    assert_eq!(bitmap.count_ones_range(2, 8), 3); // bits 3, 5, 7
    assert_eq!(bitmap.count_ones_range(0, 4), 2); // bits 1, 3

    assert_eq!(bitmap.count_zeros_range(0, 10), 5);
    assert_eq!(bitmap.count_zeros_range(2, 8), 3); // bits 2, 4, 6

    // Empty range
    assert_eq!(bitmap.count_ones_range(5, 5), 0);
    assert_eq!(bitmap.count_zeros_range(5, 5), 0);

    // Test with large bitmap
    let mut large = SmolBitmap::new();
    for i in (0..300).step_by(2) {
        large.set(i, true);
    }
    assert_eq!(large.count_ones_range(0, 100), 50);
    assert_eq!(large.count_zeros_range(0, 100), 50);
}

#[test]
fn test_batch_operations() {
    // Test set_all
    let mut bitmap = SmolBitmap::new();
    bitmap.set(0, true);
    bitmap.set(5, true);
    bitmap.set_all();

    for i in 0..=5 {
        assert!(bitmap.get(i), "Bit {i} should be set");
    }

    // Test clear_range
    let mut bitmap = SmolBitmap::new();
    for i in 0..10 {
        bitmap.set(i, true);
    }
    bitmap.clear_range(3, 7);

    assert!(bitmap.get(2));
    assert!(!bitmap.get(3));
    assert!(!bitmap.get(4));
    assert!(!bitmap.get(5));
    assert!(!bitmap.get(6));
    assert!(bitmap.get(7));

    // Test set_range_value
    let mut bitmap = SmolBitmap::new();
    bitmap.set_range_value(5, 10, true);

    assert!(!bitmap.get(4));
    for i in 5..10 {
        assert!(bitmap.get(i));
    }
    assert!(!bitmap.get(10));

    bitmap.set_range_value(7, 9, false);
    assert!(bitmap.get(6));
    assert!(!bitmap.get(7));
    assert!(!bitmap.get(8));
    assert!(bitmap.get(9));

    // Test fill
    let mut bitmap = SmolBitmap::new();
    bitmap.set(10, true); // Establishes a capacity
    bitmap.fill(true);

    for i in 0..=10 {
        assert!(bitmap.get(i));
    }

    bitmap.fill(false);
    assert!(bitmap.is_empty());
}

#[test]
fn test_from_primitive_integers() {
    // From u8
    let bitmap = SmolBitmap::from(0b10101010u8);
    assert!(!bitmap.get(0));
    assert!(bitmap.get(1));
    assert!(!bitmap.get(2));
    assert!(bitmap.get(3));
    assert!(!bitmap.get(4));
    assert!(bitmap.get(5));
    assert!(!bitmap.get(6));
    assert!(bitmap.get(7));

    // From u16
    let bitmap = SmolBitmap::from(0x1234u16);
    assert_eq!(bitmap.get_range(0, 16), 0x1234);

    // From u32
    let bitmap = SmolBitmap::from(0xDEADBEEFu32);
    assert_eq!(bitmap.get_range(0, 32), 0xDEADBEEF);

    // From u64
    let bitmap = SmolBitmap::from(0x123456789ABCDEFu64);
    assert_eq!(bitmap.get_range(0, 64), 0x123456789ABCDEFu64);

    // From u128
    let value = 0x123456789ABCDEF0123456789ABCDEFu128;
    let bitmap = SmolBitmap::from(value);
    let low = bitmap.get_range(0, 64);
    let high = bitmap.get_range(64, 128);
    assert_eq!((low as u128) | ((high as u128) << 64), value);
}

#[test]
fn test_try_from_bitmap() {
    // Successful conversions
    let mut bitmap = SmolBitmap::new();
    bitmap.set(1, true);
    bitmap.set(3, true);

    let u8_val = u8::try_from(&bitmap).unwrap();
    assert_eq!(u8_val, 0b00001010);

    let u16_val = u16::try_from(&bitmap).unwrap();
    assert_eq!(u16_val, 0b00001010);

    let u32_val = u32::try_from(&bitmap).unwrap();
    assert_eq!(u32_val, 0b00001010);

    let u64_val = u64::try_from(&bitmap).unwrap();
    assert_eq!(u64_val, 0b00001010);

    let u128_val = u128::try_from(&bitmap).unwrap();
    assert_eq!(u128_val, 0b00001010);

    // Failed conversions - too many bits
    bitmap.set(8, true); // Beyond u8 range
    assert!(u8::try_from(&bitmap).is_err());
    assert!(u16::try_from(&bitmap).is_ok());

    bitmap.set(16, true); // Beyond u16 range
    assert!(u16::try_from(&bitmap).is_err());
    assert!(u32::try_from(&bitmap).is_ok());

    bitmap.set(32, true); // Beyond u32 range
    assert!(u32::try_from(&bitmap).is_err());
    assert!(u64::try_from(&bitmap).is_ok());

    bitmap.set(64, true); // Beyond u64 range
    assert!(u64::try_from(&bitmap).is_err());
    assert!(u128::try_from(&bitmap).is_ok());

    bitmap.set(128, true); // Beyond u128 range
    match u128::try_from(&bitmap) {
        Err(TryFromBitmapError::TooManyBits {
            max_bits,
            actual_bits,
        }) => {
            assert_eq!(max_bits, 128);
            assert_eq!(actual_bits, 129);
        }
        _ => panic!("Expected TooManyBits error"),
    }
}

#[test]
fn test_bytes_conversion() {
    // Test to_bytes_le and from_bytes_le
    let mut bitmap = SmolBitmap::new();
    bitmap.set(0, true);
    bitmap.set(7, true);
    bitmap.set(8, true);
    bitmap.set(15, true);

    let bytes_le = bitmap.to_bytes_le();
    assert_eq!(bytes_le.len(), 2);
    assert_eq!(bytes_le[0], 0b10000001); // bits 0 and 7
    assert_eq!(bytes_le[1], 0b10000001); // bits 8 and 15

    let restored = SmolBitmap::from_bytes_le(&bytes_le);
    assert_eq!(bitmap, restored);

    // Test to_bytes_be and from_bytes_be
    let bytes_be = bitmap.to_bytes_be();
    let restored = SmolBitmap::from_bytes_be(&bytes_be);
    assert_eq!(bitmap, restored);

    // Test with larger bitmap
    let mut large = SmolBitmap::new();
    for i in (0..256).step_by(8) {
        large.set(i, true);
    }

    let bytes_le = large.to_bytes_le();
    let restored = SmolBitmap::from_bytes_le(&bytes_le);
    assert_eq!(large, restored);

    let bytes_be = large.to_bytes_be();
    let restored = SmolBitmap::from_bytes_be(&bytes_be);
    assert_eq!(large, restored);

    // Test empty bitmap
    let empty = SmolBitmap::new();
    let bytes_le = empty.to_bytes_le();
    assert!(bytes_le.is_empty());

    let restored = SmolBitmap::from_bytes_le(&bytes_le);
    assert_eq!(empty, restored);
}

#[test]
fn test_display_formats() {
    // Test LowerHex
    let bitmap = SmolBitmap::from(0xDEADBEEFu32);
    assert_eq!(format!("{bitmap:x}"), "deadbeef");
    assert_eq!(format!("{bitmap:#x}"), "0xdeadbeef");

    // Test UpperHex
    assert_eq!(format!("{bitmap:X}"), "DEADBEEF");
    assert_eq!(format!("{bitmap:#X}"), "0xDEADBEEF");

    // Test Octal
    let bitmap = SmolBitmap::from(0b111000u8);
    assert_eq!(format!("{bitmap:o}"), "70");
    assert_eq!(format!("{bitmap:#o}"), "0o70");

    // Test with empty bitmap
    let empty = SmolBitmap::new();
    assert_eq!(format!("{empty:x}"), "0");
    assert_eq!(format!("{empty:#x}"), "0x0");
    assert_eq!(format!("{empty:X}"), "0");
    assert_eq!(format!("{empty:#X}"), "0x0");
    assert_eq!(format!("{empty:o}"), "0");
    assert_eq!(format!("{empty:#o}"), "0o0");

    // Test with large values
    let bitmap = SmolBitmap::from(0x123456789ABCDEFu64);
    assert_eq!(format!("{bitmap:x}"), "123456789abcdef");
    assert_eq!(format!("{bitmap:X}"), "123456789ABCDEF");
}

#[test]
fn test_range_bitmap_methods() {
    let mut bitmap = SmolBitmap::new();
    bitmap.set(2, true);
    bitmap.set(3, true);
    bitmap.set(5, true);
    bitmap.set(7, true);

    // Test get_range_bitmap
    let sub = bitmap.get_range_bitmap(2, 8);
    assert!(sub.get(0)); // bit 2 -> 0
    assert!(sub.get(1)); // bit 3 -> 1
    assert!(!sub.get(2)); // bit 4 -> 2
    assert!(sub.get(3)); // bit 5 -> 3
    assert!(!sub.get(4)); // bit 6 -> 4
    assert!(sub.get(5)); // bit 7 -> 5

    // Test get_from
    let sub = bitmap.get_from(3);
    assert!(sub.get(0)); // bit 3 -> 0
    assert!(sub.get(2)); // bit 5 -> 2
    assert!(sub.get(4)); // bit 7 -> 4

    // Test get_to
    let sub = bitmap.get_to(5);
    assert!(sub.get(2));
    assert!(sub.get(3));
    assert!(!sub.get(5));
}
