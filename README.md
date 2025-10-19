# SmolBitmap

[![Crates.io](https://img.shields.io/crates/v/smol_bitmap.svg?_v=0.3.2)](https://crates.io/crates/smol_bitmap)
[![Documentation](https://docs.rs/smol_bitmap/badge.svg?_v=0.3.2)](https://docs.rs/smol_bitmap)
[![License](https://img.shields.io/crates/l/smol_bitmap.svg?_v=0.3.2)](https://github.com/can1357/smol_bitmap#license)
[![CI](https://github.com/can1357/smol_bitmap/workflows/CI/badge.svg?_v=0.3.2)](https://github.com/can1357/smol_bitmap/actions)

A space-efficient bitmap implementation with inline storage optimization for Rust.

## Features

- **Zero allocation** for bitmaps up to 127 bits
- **Automatic promotion** to heap storage for larger bitmaps
- **Rich API** with all standard set operations
- **Memory efficient** - only 16 bytes for small bitmaps
- **`no_std` support** with `alloc` for embedded systems
- **Optional serde support** for serialization
- **Excellent performance** with inline storage optimization

## Quick Start

Add to your `Cargo.toml`:

```toml
[dependencies]
smol_bitmap = "0.3.2"
```

### Basic Operations

```rust
use smol_bitmap::SmolBitmap;

fn main() {
    let mut bitmap = SmolBitmap::new();

    // Set some bits
    bitmap.insert(5);
    bitmap.insert(10);
    bitmap.insert(100);

    // Check if bits are set
    assert!(bitmap.get(5));
    assert!(!bitmap.get(6));

    // Count set bits
    assert_eq!(bitmap.count_ones(), 3);

    // Iterate over set bits
    for bit in bitmap.iter() {
        println!("Bit {} is set", bit);
    }
}
```

### Set Operations

```rust
use smol_bitmap::SmolBitmap;

fn main() {
    let mut a = SmolBitmap::new();
    a.insert(1);
    a.insert(2);
    a.insert(3);

    let mut b = SmolBitmap::new();
    b.insert(2);
    b.insert(3);
    b.insert(4);

    // Union: {1, 2, 3, 4}
    let union = a.union(&b);

    // Intersection: {2, 3}
    let intersection = a.intersection(&b);

    // Difference: {1}
    let difference = a.difference(&b);

    // Symmetric difference: {1, 4}
    let sym_diff = a.symmetric_difference(&b);
}
```

### Advanced Features

```rust
use smol_bitmap::SmolBitmap;

fn main() {
    let mut bitmap = SmolBitmap::new();

    // Reserve capacity for 500 bits
    bitmap.reserve(500);

    // Bulk operations
    bitmap.extend([10, 20, 30, 40, 50]);

    // Retain only even indices
    bitmap.retain(|bit| bit % 2 == 0);

    // Find next/previous set bits
    assert_eq!(bitmap.next_set_bit(15), Some(20));
    assert_eq!(bitmap.prev_set_bit(35), Some(30));

    // Toggle bits
    bitmap.complement(25);

    // Create from iterator
    let from_iter: SmolBitmap = (0..10).step_by(2).collect();
}
```

## Performance

SmolBitmap uses a hybrid storage strategy optimized for both small and large bitmaps:

### Storage Layout

- **Inline Storage** (≤127 bits): Stored directly in 16 bytes, no heap allocation
- **Heap Storage** (>127 bits): Automatically promotes to `Vec<u64>` when needed

### Benchmarks

Performance comparison with `bitvec` (lower is better):

| Operation       | Size       | SmolBitmap | BitVec  | Winner                       |
| --------------- | ---------- | ---------- | ------- | ---------------------------- |
| **Creation**    | 100 bits   | 2.6ns      | 15.7ns  | **SmolBitmap** (6.0x faster) |
|                 | 1000 bits  | 11.4ns     | 14.1ns  | **SmolBitmap** (1.2x faster) |
|                 | 10000 bits | 47.5ns     | 66.3ns  | **SmolBitmap** (1.4x faster) |
| **Set bit**     | 100 bits   | 12.8ns     | 28.3ns  | **SmolBitmap** (2.2x faster) |
|                 | 1000 bits  | 132.6ns    | 97.2ns  | BitVec (1.4x faster)         |
|                 | 10000 bits | 163.8ns    | 138.8ns | BitVec (1.2x faster)         |
| **Get bit** ¹   | 100 bits   | 528ns      | 514ns   | -                            |
|                 | 1000 bits  | 648ns      | 535ns   | BitVec (1.2x faster)         |
|                 | 10000 bits | 624ns      | 509ns   | BitVec (1.2x faster)         |
| **Iteration** ² | 100 bits   | 19.3ns     | 71.9ns  | **SmolBitmap** (3.7x faster) |
|                 | 1000 bits  | 376ns      | 701ns   | **SmolBitmap** (1.9x faster) |
|                 | 10000 bits | 3.98µs     | 6.32µs  | **SmolBitmap** (1.6x faster) |
| **Count ones**  | 100 bits   | 2.2ns      | 3.0ns   | **SmolBitmap** (1.4x faster) |
|                 | 1000 bits  | 1.8ns      | 6.8ns   | **SmolBitmap** (3.8x faster) |
|                 | 10000 bits | 17.4ns     | 11.1ns  | BitVec (1.6x faster)         |

¹ Time for N get operations  
² Sparse bitmap iteration (every 10th bit set)

**Key Advantages:**

- **Memory**: 16 bytes for SmolBitmap vs 24+ bytes for BitVec
- **Small bitmaps**: Zero allocation for up to 127 bits
- **Iteration**: Word-skipping optimization provides consistent wins
- **Cache locality**: Better performance for small-to-medium bitmaps

Run benchmarks yourself:

```bash
cargo bench
```

## When to Use

✅ Best when:

- You manage _lots of small bitmaps_ (flags, sets, indexes)
- Most stay under 128 bits but a few grow larger
- Iteration speed and memory footprint matter

❌ Prefer alternatives when:

- All bitmaps are very large (>1000 bits) → `bit-vec` / `bitvec`
- You need fixed-size → `fixedbitset`
- You need compression → `roaring`

## Examples

See the [`examples/`](examples/) directory for more usage examples:

```bash
# Basic usage
cargo run --example basic

# Advanced features
cargo run --example advanced
```

## Feature Flags

- `std` (default) - Use standard library (provides `Error` trait implementation)
- `serde` - Enable serialization/deserialization support

## No-std Usage

SmolBitmap supports `no_std` environments with `alloc`:

```toml
[dependencies]
smol_bitmap = { version = "0.3.2", default-features = false }
```

This will disable the `std` feature but still requires an allocator for heap storage when bitmaps exceed inline capacity.

## Safety

SmolBitmap uses `unsafe` code in a few performance-critical areas. All unsafe usage is:

- Carefully documented with safety invariants
- Minimal in scope
- Covered by tests
- Audited for correctness

## Contributing

Contributions are welcome! Please feel free to submit a Pull Request.

## License

This project is licensed under the MIT license.
