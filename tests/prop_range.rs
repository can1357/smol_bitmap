use proptest::prelude::*;
use smol_bitmap::SmolBitmap;

// Strategy for generating bitmaps with various patterns
prop_compose! {
    fn arb_bitmap(max_bits: usize)
        (bits in prop::collection::vec((0..max_bits, bool::arbitrary()), 0..100))
        -> SmolBitmap
    {
        let mut bitmap = SmolBitmap::new();
        for (idx, value) in bits {
            bitmap.set(idx, value);
        }
        bitmap
    }
}

// Strategy for generating dense bitmaps
prop_compose! {
    fn dense_bitmap()
        (words in prop::collection::vec(any::<u64>(), 1..=5))
        -> SmolBitmap
    {
        SmolBitmap::from(words.as_slice())
    }
}

proptest! {
    #[test]
    fn test_take_preserves_bits(
        bitmap in arb_bitmap(300),
        end in 0usize..400
    ) {
        let sub = bitmap.take(end);

        // Every bit in the result should match the original
        for i in 0..end {
            prop_assert_eq!(
                sub.get(i),
                bitmap.get(i),
                "Bit {} mismatch: expected {}, got {}",
                i, bitmap.get(i), sub.get(i)
            );
        }

        // No bits should be set beyond the end
        if let Some(last) = sub.last() {
            prop_assert!(
                last < end,
                "Found bit {} set, but end was {}",
                last, end
            );
        }
    }

    #[test]
    fn test_skip_preserves_bits(
        bitmap in arb_bitmap(300),
        start in 0usize..400
    ) {
        let sub = bitmap.skip(start);

        // Check that bits are correctly shifted
        for original_idx in start..400 {
            let new_idx = original_idx - start;
            prop_assert_eq!(
                sub.get(new_idx),
                bitmap.get(original_idx),
                "Bit {} (originally {}) mismatch",
                new_idx, original_idx
            );
        }
    }

    #[test]
    fn test_bitslice_preserves_bits(
        bitmap in arb_bitmap(300),
        start in 0usize..300,
        len in 0usize..200
    ) {
        let end = start + len;
        let sub = bitmap.bitslice(start, end);

        // Check each bit in the range
        for i in 0..len {
            prop_assert_eq!(
                sub.get(i),
                bitmap.get(start + i),
                "Bit {} (originally {}) mismatch",
                i, start + i
            );
        }

        // Verify no extra bits are set
        if let Some(last) = sub.last() {
            prop_assert!(
                last < len,
                "Found bit {} set, but range length was {}",
                last, len
            );
        }
    }

    #[test]
    fn test_bigint_vs_smolbitmap_shr(
        bitmap in arb_bitmap(512),
        shift_amount in 0usize..400
    ) {
        // Convert SmolBitmap to BigInt
        let bigint = num_bigint::BigInt::from_bytes_le(num_bigint::Sign::Plus, bitmap.to_le_bytes().as_ref());

        // Perform shift operations
        let smol_bitmap_shifted = bitmap.shr(shift_amount);
        let bigint_shifted = bigint >> shift_amount;

        // Convert shifted BigInt back to SmolBitmap
        let bitmap_as_bigint = num_bigint::BigInt::from_bytes_le(num_bigint::Sign::Plus, smol_bitmap_shifted.to_le_bytes().as_ref());

        // Compare the results
        prop_assert_eq!(
            bigint_shifted, bitmap_as_bigint,
            "Mismatch between SmolBitmap and BigInt shift results for shift amount {}",
            shift_amount
        );
    }

    #[test]
    fn test_range_composition(
        bitmap in dense_bitmap(),
        start in 0usize..200,
        end in 0usize..200
    ) {
        let start = start.min(end);
        let end = start.max(end);

        // bitslice(start, end) should equal manually extracted bits
        let range_direct = bitmap.bitslice(start, end);
        let mut range_manual = SmolBitmap::new();
        for (offset, i) in (start..end).enumerate() {
            range_manual.set(offset, bitmap.get(i));
        }
        prop_assert_eq!(&range_direct, &range_manual, "Mismatch for range [{}, {})", start, end);


        // bitslice(start, end) should equal skip(start).take(end - start)
        let range_composed = bitmap.skip(start).take(end - start);

        // Compare word by word for efficiency
        prop_assert_eq!(
            &range_direct,
            &range_composed,
            "Mismatch for range [{}, {})",
            start, end
        );
    }

    #[test]
    fn test_take_from_inverse(
        bitmap in arb_bitmap(200),
        split in 0usize..250
    ) {
        let left = bitmap.take(split);
        let right = bitmap.skip(split);

        // Verify that combining left and right recreates the original
        for i in 0..400 {
            let expected = bitmap.get(i);
            let actual = if i < split {
                left.get(i)
            } else {
                right.get(i - split)
            };
            prop_assert_eq!(
                actual, expected,
                "Bit {} mismatch after split at {}",
                i, split
            );
        }
    }

    #[test]
    fn test_aligned_operations(
        words in prop::collection::vec(any::<u64>(), 1..5)
    ) {
        let bitmap = SmolBitmap::from(words.as_slice());

        // Test word-aligned boundaries
        for word_idx in 0..=words.len() {
            let bit_idx = word_idx * 64;

            // take at word boundary
            let to_result = bitmap.take(bit_idx);
            for i in 0..bit_idx {
                prop_assert_eq!(to_result.get(i), bitmap.get(i));
            }

            // skip at word boundary
            let from_result = bitmap.skip(bit_idx);
            for i in 0..200 {
                prop_assert_eq!(from_result.get(i), bitmap.get(bit_idx + i));
            }
        }
    }

    #[test]
    fn test_misaligned_operations(
        words in prop::collection::vec(any::<u64>(), 2..5),
        offset in 1usize..63
    ) {
        let bitmap = SmolBitmap::from(words.as_slice());

        // Test operations at non-word boundaries
        for word_idx in 0..words.len() {
            let bit_idx = word_idx * 64 + offset;

            let to_result = bitmap.take(bit_idx);
            let from_result = bitmap.skip(bit_idx);
            let range_result = bitmap.bitslice(offset, bit_idx);

            // Verify correctness
            for i in 0..bit_idx {
                prop_assert_eq!(to_result.get(i), bitmap.get(i));
            }

            for i in 0..100 {
                prop_assert_eq!(from_result.get(i), bitmap.get(bit_idx + i));
            }

            for i in 0..(bit_idx - offset) {
                prop_assert_eq!(range_result.get(i), bitmap.get(offset + i));
            }
        }
    }

    #[test]
    fn test_empty_ranges(
        bitmap in arb_bitmap(200),
        idx in 0usize..300
    ) {
        // Empty range should produce empty bitmap
        let empty = bitmap.bitslice(idx, idx);
        prop_assert!(empty.is_empty());

        // Reversed range should produce empty bitmap
        if idx > 0 {
            let reversed = bitmap.bitslice(idx, idx - 1);
            prop_assert!(reversed.is_empty());
        }
    }

    #[test]
    fn test_beyond_capacity(
        bitmap in arb_bitmap(100)
    ) {
        let cap = bitmap.capacity();

        // Operations beyond capacity should handle gracefully
        let beyond_from = bitmap.skip(cap + 100);
        prop_assert!(beyond_from.is_empty());

        let beyond_to = bitmap.take(cap + 100);
        // Should contain all bits from original
        for i in 0..cap {
            prop_assert_eq!(beyond_to.get(i), bitmap.get(i));
        }

        let beyond_range = bitmap.bitslice(cap + 10, cap + 20);
        prop_assert!(beyond_range.is_empty());
    }

    #[test]
    fn test_single_bit_ranges(
        idx in 0usize..200
    ) {
        let mut bitmap = SmolBitmap::new();
        bitmap.insert(idx);

        // Extract just that single bit
        let single = bitmap.bitslice(idx, idx + 1);
        prop_assert!(single.get(0));
        assert_eq!(single.count_ones(), 1);

        // Extract up to that bit (exclusive)
        let up_to = bitmap.take(idx);
        prop_assert!(!up_to.get(idx));
        assert_eq!(up_to.count_ones(), 0);

        // Extract from that bit
        let from = bitmap.skip(idx);
        prop_assert!(from.get(0));
        assert_eq!(from.count_ones(), 1);
    }

    #[test]
    fn test_sparse_bitmap_ranges(
        positions in prop::collection::hash_set(0usize..500, 0..50)
    ) {
        let mut bitmap = SmolBitmap::new();
        for &pos in &positions {
            bitmap.insert(pos);
        }

        // Test various range extractions preserve sparsity
        for &split in &[50, 100, 200, 300] {
            let left = bitmap.take(split);
            let right = bitmap.skip(split);

            let left_count = positions.iter().filter(|&&p| p < split).count();
            let right_count = positions.iter().filter(|&&p| p >= split).count();

            prop_assert_eq!(left.count_ones(), left_count);
            prop_assert_eq!(right.count_ones(), right_count);
        }
    }

    #[test]
    fn test_inline_to_heap_transition(
        start in 0usize..127,
        end in 0usize..200
    ) {
        let mut bitmap = SmolBitmap::new();
        // Set bits to force different storage modes
        bitmap.insert(0);
        bitmap.insert(126);  // Still inline

        let sub1 = bitmap.bitslice(start, end.min(127));
        prop_assert!(!sub1.is_spilled() || sub1.is_empty());

        bitmap.insert(200);  // Force heap
        let sub2 = bitmap.bitslice(start, end);

        // Verify bits are preserved regardless of storage mode
        for i in start..end.min(127) {
            prop_assert_eq!(
                sub1.get(i - start),
                sub2.get(i - start)
            );
        }
    }

    #[test]
    fn test_word_boundary_edge_cases(
        word1 in any::<u64>(),
        word2 in any::<u64>(),
        word3 in any::<u64>()
    ) {
        let bitmap = SmolBitmap::from(&[word1, word2, word3][..]);

        // Test extraction exactly at word boundaries
        let first_word = bitmap.extract_word(0);
        let second_word = bitmap.extract_word(1);
        let third_word = bitmap.extract_word(2);

        prop_assert_eq!(first_word, word1);
        prop_assert_eq!(second_word, word2);
        prop_assert_eq!(third_word, word3);

        // Test spanning word boundaries
        let span = bitmap.get_range(32, 96);
        for i in 0..64 {
            prop_assert_eq!(((span >> i) & 1) != 0, bitmap.get(32 + i));
        }
    }
}
