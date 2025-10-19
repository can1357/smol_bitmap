use smol_bitmap::{SmolBitmap, TryFromBitmapError};
use std::{collections::BTreeSet, convert::TryFrom};

#[test]
fn test_inline_storage() {
    let mut mask = SmolBitmap::new();

    // Test inline storage capacity
    for i in 0..SmolBitmap::inline_capacity() {
        assert!(!mask.get(i));
        mask.insert(i);
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
    bitmap.insert(200);
    assert!(bitmap.get(200));
}

#[test]
fn test_highest_inline_bit_forces_external() {
    let mut bitmap = SmolBitmap::new();
    let highest_inline_bit = SmolBitmap::inline_capacity();

    // Set the bit at inline capacity (which is beyond inline storage)
    bitmap.insert(highest_inline_bit);

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
    mask.insert(inline_cap);
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

    a.insert(10);
    a.insert(20);
    a.insert(30);
    b.insert(20);
    b.insert(30);
    b.insert(40);

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
    bitmap.insert(0);
    bitmap.insert(10);
    bitmap.insert(63);
    bitmap.insert(64);
    bitmap.insert(100);
    bitmap.insert(200);

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

    a.insert(10);
    assert_ne!(a, b);
    assert!(a > b); // Non-empty > empty

    b.insert(10);
    assert_eq!(a, b);

    b.insert(20);
    assert!(a < b); // {10} < {10, 20}
}

#[test]
fn test_shrink_to_fit() {
    let mut bitmap = SmolBitmap::new();

    // Set a high bit then clear it
    bitmap.insert(300);
    assert!(bitmap.is_spilled());
    bitmap.remove(300);

    // Set a low bit
    bitmap.insert(50);

    bitmap.shrink_to_fit();
    // Should potentially move back to inline if possible
    assert!(bitmap.get(50));
    assert!(!bitmap.get(300));
}

#[test]
fn test_exact_size_iterator() {
    let mut bitmap = SmolBitmap::new();
    for i in (0..300).step_by(2) {
        bitmap.insert(i);
    }

    let iter = bitmap.iter();
    assert_eq!(iter.len(), 150);
    assert_eq!(iter.count(), 150);
}

#[test]
fn test_retain() {
    let mut bitmap = SmolBitmap::new();
    bitmap.insert(1);
    bitmap.insert(2);
    bitmap.insert(5);
    bitmap.insert(8);
    bitmap.insert(10);
    bitmap.insert(15);

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
    bitmap.insert(5);
    bitmap.insert(100);
    bitmap.insert(200);

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
                bitmap.insert(idx);
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
                a.insert(idx);
            }
            for &idx in &indices_b {
                b.insert(idx);
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
                a.insert(idx);
            }
            for &idx in &indices_b {
                b.insert(idx);
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
    a.insert(0);
    a.insert(1);
    a.insert(3);

    let mut b = SmolBitmap::new();
    b.insert(1);
    b.insert(2);
    b.insert(3);

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
#[allow(clippy::many_single_char_names)]
fn test_bitwise_assign_operators() {
    // Test BitAndAssign (&=)
    let mut a = SmolBitmap::new();
    a.insert(0);
    a.insert(1);
    a.insert(3);

    let mut b = SmolBitmap::new();
    b.insert(1);
    b.insert(2);
    b.insert(3);

    a &= &b;
    assert!(!a.get(0)); // Was only in a, removed
    assert!(a.get(1)); // In both, kept
    assert!(!a.get(2)); // Not in a
    assert!(a.get(3)); // In both, kept

    // Test BitOrAssign (|=)
    let mut c = SmolBitmap::new();
    c.insert(0);
    c.insert(1);

    let mut d = SmolBitmap::new();
    d.insert(2);
    d.insert(3);

    c |= &d;
    assert!(c.get(0));
    assert!(c.get(1));
    assert!(c.get(2));
    assert!(c.get(3));

    // Test BitXorAssign (^=)
    let mut e = SmolBitmap::new();
    e.insert(0);
    e.insert(1);
    e.insert(3);

    let mut f = SmolBitmap::new();
    f.insert(1);
    f.insert(2);
    f.insert(3);

    e ^= &f;
    assert!(e.get(0)); // Only in original e
    assert!(!e.get(1)); // In both, removed
    assert!(e.get(2)); // Only in f, added
    assert!(!e.get(3)); // In both, removed
}

#[test]
fn test_not_operator() {
    let mut a = SmolBitmap::new();
    a.insert(0);
    a.insert(2);
    a.insert(4);

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
    a.insert(150);
    a.insert(200);
    a.insert(250);

    let mut b = SmolBitmap::new();
    b.insert(200);
    b.insert(250);
    b.insert(300);

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
    bitmap.insert(0);
    bitmap.insert(1);
    bitmap.insert(2);

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
fn test_shift_operations_spilled() {
    // Test with spilled storage
    let mut bitmap = SmolBitmap::new();
    bitmap.insert(150);
    bitmap.insert(200);

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
    bitmap.insert(5);
    assert!(bitmap.any());
    assert!(!bitmap.all()); // Not all bits from 0-5 are set
    assert!(!bitmap.none());

    // Multiple consecutive bits
    bitmap.insert(0);
    bitmap.insert(1);
    bitmap.insert(2);
    bitmap.insert(3);
    bitmap.insert(4);
    assert!(bitmap.any());
    assert!(bitmap.all()); // All bits 0-5 are set
    assert!(!bitmap.none());

    // Gap in bits
    bitmap.insert(7);
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
    bitmap.insert(5);
    assert_eq!(bitmap.leading_zeros(), Some(5)); // 5 leading zeros (bits 0-4)
    assert_eq!(bitmap.trailing_zeros(), Some(5)); // 5 trailing zeros from bit 5 down to bit 0

    // Add bit at position 0
    bitmap.insert(0);
    assert_eq!(bitmap.leading_zeros(), Some(0)); // No leading zeros
    assert_eq!(bitmap.trailing_zeros(), Some(4)); // 4 trailing zeros from bit 5 down to bit 1 (bit 0 is set)

    // Add bit at position 10, leaving gap
    bitmap.insert(10);
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
    bitmap.insert(0);
    bitmap.insert(1);
    bitmap.insert(2);
    assert_eq!(bitmap.leading_ones(), 3);
    assert_eq!(bitmap.trailing_ones(), 3);

    // Add gap and more bits
    bitmap.insert(5);
    bitmap.insert(6);
    bitmap.insert(7);
    assert_eq!(bitmap.leading_ones(), 3); // Still 3 (stops at bit 3)
    assert_eq!(bitmap.trailing_ones(), 3); // 3 consecutive from bit 7 down to 5
}

// ============================================================================
// Tests for Range Operations
// ============================================================================

#[test]
fn test_get_range() {
    let mut bitmap = SmolBitmap::new();
    bitmap.insert(0);
    bitmap.insert(2);
    bitmap.insert(3);
    bitmap.insert(5);

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
            large.insert(i);
        }
    }
    // Should only extract first 64 bits
    let extracted = large.get_range(0, 100);
    assert_eq!(extracted.count_ones(), 32); // Every other bit for 64 bits
}

#[test]
#[should_panic(expected = "beg must be <= end")]
fn test_get_range_panic() {
    let bitmap = SmolBitmap::new();
    _ = bitmap.get_range(10, 5); // start > end
}

// ============================================================================
// Additional Tests for New Features
// ============================================================================

#[test]
fn test_index_trait() {
    use core::ops::Index;

    let mut bitmap = SmolBitmap::new();
    bitmap.insert(5);
    bitmap.insert(10);

    // Test Index<usize>
    assert!(*bitmap.index(5));
    assert!(*bitmap.index(10));
    assert!(!(*bitmap.index(0)));
    assert!(!(*bitmap.index(6)));

    // Test with spilled storage
    bitmap.insert(200);
    assert!(*bitmap.index(200));
    assert!(!(*bitmap.index(199)));
}

#[test]
fn test_index_no_panic() {
    use core::ops::Index;

    let bitmap = SmolBitmap::new();
    // Index trait now returns false for out-of-bounds, consistent with get()
    assert!(!(*bitmap.index(1000))); // Beyond capacity returns false
    assert!(!(*bitmap.index(0))); // Unset bit returns false

    let mut bitmap = SmolBitmap::new();
    bitmap.insert(5);
    assert!(*bitmap.index(5)); // Set bit returns true
}

#[test]
fn test_find_zero_methods() {
    let mut bitmap = SmolBitmap::new();

    // Empty bitmap - all zeros
    assert_eq!(bitmap.find_first_zero(), Some(0));
    assert_eq!(bitmap.find_last_zero(), Some(0));

    // Set some bits
    bitmap.insert(0);
    bitmap.insert(1);
    bitmap.insert(3);
    bitmap.insert(5);

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
        large.insert(i);
    }
    assert_eq!(large.find_first_zero(), Some(200));

    large.remove(150);
    assert_eq!(large.find_first_zero(), Some(150));
}

#[test]
fn test_count_range_methods() {
    let mut bitmap = SmolBitmap::new();
    bitmap.insert(1);
    bitmap.insert(3);
    bitmap.insert(5);
    bitmap.insert(7);
    bitmap.insert(9);

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
        large.insert(i);
    }
    assert_eq!(large.count_ones_range(0, 100), 50);
    assert_eq!(large.count_zeros_range(0, 100), 50);
}

#[test]
fn test_batch_operations() {
    // Test set_all
    let mut bitmap = SmolBitmap::new();
    bitmap.insert(0);
    bitmap.insert(5);
    bitmap.set_all();

    for i in 0..=5 {
        assert!(bitmap.get(i), "Bit {i} should be set");
    }

    // Test clear_range
    let mut bitmap = SmolBitmap::new();
    for i in 0..10 {
        bitmap.insert(i);
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
    bitmap.insert(10); // Establishes a capacity
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
    assert_eq!(u128::from(low) | (u128::from(high) << 64), value);
}

#[test]
fn test_try_from_bitmap() {
    // Successful conversions
    let mut bitmap = SmolBitmap::new();
    bitmap.insert(1);
    bitmap.insert(3);

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
    bitmap.insert(8); // Beyond u8 range
    assert!(u8::try_from(&bitmap).is_err());
    assert!(u16::try_from(&bitmap).is_ok());

    bitmap.insert(16); // Beyond u16 range
    assert!(u16::try_from(&bitmap).is_err());
    assert!(u32::try_from(&bitmap).is_ok());

    bitmap.insert(32); // Beyond u32 range
    assert!(u32::try_from(&bitmap).is_err());
    assert!(u64::try_from(&bitmap).is_ok());

    bitmap.insert(64); // Beyond u64 range
    assert!(u64::try_from(&bitmap).is_err());
    assert!(u128::try_from(&bitmap).is_ok());

    bitmap.insert(128); // Beyond u128 range
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
    // Test to_le_bytes and from_le_bytes
    let mut bitmap = SmolBitmap::new();
    bitmap.insert(0);
    bitmap.insert(7);
    bitmap.insert(8);
    bitmap.insert(15);

    let le = bitmap.to_le_bytes();
    assert_eq!(le[0], 0b10000001); // bits 0 and 7
    assert_eq!(le[1], 0b10000001); // bits 8 and 15
    assert!(le[2..].iter().all(|&b| b == 0));

    let (restored, _) = SmolBitmap::from_le_bytes(&le);
    assert_eq!(bitmap, restored);

    // Test to_be_bytes and from_be_bytes
    let be = bitmap.to_be_bytes();
    let (restored, _) = SmolBitmap::from_be_bytes(&be);
    assert_eq!(bitmap, restored);

    // Test with larger bitmap
    let mut large = SmolBitmap::new();
    for i in (0..256).step_by(8) {
        large.insert(i);
    }

    let le = large.to_le_bytes();
    let (restored, _) = SmolBitmap::from_le_bytes(&le);
    assert_eq!(large, restored);

    let be = large.to_be_bytes();
    let (restored, _) = SmolBitmap::from_be_bytes(&be);
    assert_eq!(large, restored);

    // Test empty bitmap
    let empty = SmolBitmap::new();
    let le = empty.to_le_bytes();
    assert!(le.is_empty());

    let (restored, _) = SmolBitmap::from_le_bytes(&le);
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
    bitmap.insert(2);
    bitmap.insert(3);
    bitmap.insert(5);
    bitmap.insert(7);

    // Test bitslice
    let sub = bitmap.bitslice(2, 8);
    assert!(sub.get(0)); // bit 2 -> 0
    assert!(sub.get(1)); // bit 3 -> 1
    assert!(!sub.get(2)); // bit 4 -> 2
    assert!(sub.get(3)); // bit 5 -> 3
    assert!(!sub.get(4)); // bit 6 -> 4
    assert!(sub.get(5)); // bit 7 -> 5

    // Test skip
    let sub = bitmap.skip(3);
    assert!(sub.get(0)); // bit 3 -> 0
    assert!(sub.get(2)); // bit 5 -> 2
    assert!(sub.get(4)); // bit 7 -> 4

    // Test take
    let sub = bitmap.take(5);
    assert!(sub.get(2));
    assert!(sub.get(3));
    assert!(!sub.get(5));
}
