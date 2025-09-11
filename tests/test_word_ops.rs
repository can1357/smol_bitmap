use smol_bitmap::SmolBitmap;

#[test]
fn test_extract_word_basic() {
    let mut bitmap = SmolBitmap::new();

    // Set some bits in word 0
    bitmap.insert(0);
    bitmap.insert(1);
    bitmap.insert(63);

    let word0 = bitmap.extract_word(0);
    assert_eq!(word0, (1u64 << 63) | 3);

    // Extract non-existent word
    assert_eq!(bitmap.extract_word(5), 0);
}

#[test]
fn test_extract_word_inline_bit_127() {
    let mut bitmap = SmolBitmap::new();

    // Set bits in word 1, including bit 126 but not 127
    bitmap.insert(64);
    bitmap.insert(126);

    // Extract word 1 - bit 127 should be masked
    let word1 = bitmap.extract_word(1);
    assert_eq!(word1, (1u64 << 62) | 1); // bits 64 and 126 mapped to 0 and 62
    assert!(!bitmap.is_spilled());
}

#[test]
fn test_put_word_basic() {
    let mut bitmap = SmolBitmap::new();

    // Put a word at index 0
    bitmap.put_word(0, 0xDEADBEEF);
    assert_eq!(bitmap.extract_word(0), 0xDEADBEEF);
    assert!(!bitmap.is_spilled());

    // Verify individual bits
    for i in 0..32 {
        assert_eq!(bitmap.get(i), ((0xDEADBEEFu64 >> i) & 1) != 0);
    }
}

#[test]
fn test_put_word_promotion() {
    let mut bitmap = SmolBitmap::new();

    // Put a word at index 1 without MSB - should stay inline
    bitmap.put_word(1, 0x7FFF_FFFF_FFFF_FFFF);
    assert!(!bitmap.is_spilled());
    assert_eq!(bitmap.extract_word(1), 0x7FFF_FFFF_FFFF_FFFF);

    // Put a word at index 1 with MSB set - should promote to heap
    bitmap.put_word(1, 0x8000_0000_0000_0000);
    assert!(bitmap.is_spilled());
    assert_eq!(bitmap.extract_word(1), 0x8000_0000_0000_0000);

    // Verify bit 127 is actually set after promotion
    assert!(bitmap.get(127));
}

#[test]
fn test_put_word_extend() {
    let mut bitmap = SmolBitmap::new();

    // Put a word at a high index - should allocate space
    bitmap.put_word(10, 0x1234_5678_9ABC_DEF0);
    assert!(bitmap.is_spilled()); // Extended beyond inline capacity
    assert_eq!(bitmap.extract_word(10), 0x1234_5678_9ABC_DEF0);

    // Verify intermediate words are zero
    for i in 0..10 {
        assert_eq!(bitmap.extract_word(i), 0);
    }
}

#[test]
fn test_word_ops_roundtrip() {
    let mut bitmap = SmolBitmap::new();

    // Test various bit patterns
    let patterns = [
        0x0000_0000_0000_0000,
        0xFFFF_FFFF_FFFF_FFFF,
        0xAAAA_AAAA_AAAA_AAAA,
        0x5555_5555_5555_5555,
        0x0F0F_0F0F_0F0F_0F0F,
        0xF0F0_F0F0_F0F0_F0F0,
    ];

    // Test word 0 (always safe)
    for &pattern in &patterns {
        bitmap.put_word(0, pattern);
        assert_eq!(bitmap.extract_word(0), pattern);
    }

    // Test word 1 with safe patterns (no MSB)
    for &pattern in &patterns {
        let safe_pattern = pattern & !(1u64 << 63);
        bitmap.put_word(1, safe_pattern);
        assert_eq!(bitmap.extract_word(1), safe_pattern);
        assert!(!bitmap.is_spilled());
    }
}

#[test]
fn test_extract_word_after_spill() {
    let mut bitmap = SmolBitmap::new();

    // Fill with pattern
    bitmap.put_word(0, 0x1111_1111_1111_1111);
    bitmap.put_word(1, 0x2222_2222_2222_2222);

    // Force spill by setting bit 127
    bitmap.insert(127);
    assert!(bitmap.is_spilled());

    // Extract should work the same after spill
    assert_eq!(bitmap.extract_word(0), 0x1111_1111_1111_1111);
    assert_eq!(bitmap.extract_word(1), 0x2222_2222_2222_2222 | (1u64 << 63));
}

#[test]
fn test_put_word_updates_existing() {
    let mut bitmap = SmolBitmap::new();

    // Initial word
    bitmap.put_word(0, 0xAAAA_AAAA_AAAA_AAAA);
    assert_eq!(bitmap.extract_word(0), 0xAAAA_AAAA_AAAA_AAAA);

    // Update the same word
    bitmap.put_word(0, 0x5555_5555_5555_5555);
    assert_eq!(bitmap.extract_word(0), 0x5555_5555_5555_5555);

    // Original bits should be replaced
    for i in 0..64 {
        assert_eq!(bitmap.get(i), ((0x5555_5555_5555_5555u64 >> i) & 1) != 0);
    }
}
