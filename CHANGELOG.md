# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

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
