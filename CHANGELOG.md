# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [0.3.2] - 2025-10-20

### Added

- **`bitmap!` macro**: Convenient macro for creating `SmolBitmap` instances from a list of bit positions
  - Automatically determines required capacity based on maximum bit position
  - Supports empty bitmaps and works with both inline and heap storage
  - Handles duplicate bits and unordered input gracefully
  - Comprehensive test coverage

### Changed

- **Code quality improvements**: Added comprehensive Clippy linting configuration with aggressive warning levels for better code quality

### Fixed

- **Method annotations**: Added `#[must_use]` attributes to appropriate methods for better API ergonomics

## [0.3.1] - 2025-09-19

### Fixed

- **Rkyv Support**: Updated to dynamically discover the archived type of `u64` instead of hardcoding it. This change ensures compatibility with future versions and features of `rkyv` and improves the flexibility of the archival process.

## [0.3.0] - 2025-09-19

### Added

- **Serde support** with multiple serialization formats:

  - `words`: Serialize as a sequence of u64 words (compact for dense bitmaps)
  - `sorted_set`: Serialize as a sorted sequence of set bit indices (efficient for sparse bitmaps)
  - `unordered_set`: Serialize as an unordered sequence of set bit indices
  - `le_bytes`, `be_bytes`, `ne_bytes`: Serialize as byte arrays with specified endianness
  - Default implementation uses little-endian bytes for binary formats and base64-encoded strings for human-readable formats
  - Comprehensive test coverage using `serde_test`

- **Rkyv support** for zero-copy deserialization:
  - Efficient archival format using little-endian u64 words
  - Compatible with `rkyv` 0.8

### Changed

- Made `serde` an optional feature (enabled by default)
- Added `rkyv` as an optional feature
- Added `data-encoding` dependency for base64 support in human-readable serde formats

## [0.2.2] - 2025-09-11

### Changed

- **BREAKING**: Renamed `position_of()` to `rank()` for consistency
- **BREAKING**: Renamed `toggle()` to `complement()` and now returns the previous bit value
- **BREAKING**: Renamed `exchange()` to `replace()` for consistency with standard library naming
- **BREAKING**: Removed `complement(max_bit)` method that created a new bitmap (use `complement_range()` instead)
- **BREAKING**: Renamed range extraction methods for clarity:
  - `get_range_bitmap()` → `bitslice()`
  - `get_from()` → `skip()`
  - `get_to()` → `take()`

### Added

- `complement_range(beg, end)` method for complementing bits in a range
- `extract_word(idx)` and `put_word(idx, word)` for direct 64-bit word manipulation
- `resize(new_bits)` and `truncate(max_bits)` methods for dynamic size management
- `to_ne_bytes()` and `from_ne_bytes()` for native-endian byte conversion
- `eq_rtrim()` and `cmp_rtrim()` for comparisons ignoring trailing zeros
- `contains()` as an alias for `get()`
- `add()` as an alias for `insert()`
- `cardinality()` as an alias for `count_ones()`
- Made `as_slice_rtrim()` public for accessing trimmed storage

### Fixed

- Improved handling of word boundary operations
- More consistent behavior across inline and heap storage modes
- Better performance for shift operations through optimized carry handling

### Performance

- Optimized `SmolBitmapBuilder` with inline `StackVec` implementation
- Improved `bitslice()` implementation for better efficiency
- Optimized complement operations to work in-place
- More efficient shift operations with better bit manipulation

### Internal

- Added `num-bigint` as a dev dependency for property-based testing
- Expanded test coverage with property-based tests for range operations
- Improved documentation and examples throughout
