//! Benchmark comparison between `SmolBitmap` and bitvec

use bitvec::prelude::*;
use core::hint::black_box;
use criterion::{BenchmarkId, Criterion, Throughput, criterion_group, criterion_main};
use smol_bitmap::SmolBitmap;

// Test different sizes to compare inline vs heap performance
const SIZES: &[usize] = &[10, 50, 100, 500, 1000, 5000, 10000];

fn bench_creation(c: &mut Criterion) {
    let mut group = c.benchmark_group("creation");

    for &size in SIZES {
        group.throughput(Throughput::Elements(size as u64));

        group.bench_with_input(BenchmarkId::new("SmolBitmap", size), &size, |b, &size| {
            b.iter(|| {
                let mut bitmap = SmolBitmap::with_capacity(size);
                black_box(&mut bitmap);
            });
        });

        group.bench_with_input(BenchmarkId::new("BitVec", size), &size, |b, &size| {
            b.iter(|| {
                let mut bitvec = BitVec::<u64, Lsb0>::with_capacity(size);
                bitvec.resize(size, false);
                black_box(&mut bitvec);
            });
        });
    }

    group.finish();
}

fn bench_set_operations(c: &mut Criterion) {
    let mut group = c.benchmark_group("set_bit");

    for &size in SIZES {
        group.throughput(Throughput::Elements(100));

        // Sparse set pattern (every 10th bit)
        let indices: Vec<usize> = (0..size).step_by(10).take(100).collect();

        group.bench_with_input(
            BenchmarkId::new("SmolBitmap", size),
            &indices,
            |b, indices| {
                b.iter(|| {
                    let mut bitmap = SmolBitmap::with_capacity(size);
                    for &i in indices {
                        bitmap.insert(i);
                    }
                    black_box(&bitmap);
                });
            },
        );

        group.bench_with_input(BenchmarkId::new("BitVec", size), &indices, |b, indices| {
            b.iter(|| {
                let mut bitvec = BitVec::<u64, Lsb0>::with_capacity(size);
                bitvec.resize(size, false);
                for &i in indices {
                    bitvec.insert(i, true);
                }
                black_box(&bitvec);
            });
        });
    }

    group.finish();
}

fn bench_get_operations(c: &mut Criterion) {
    let mut group = c.benchmark_group("get_bit");

    for &size in &[100, 1000, 10000] {
        group.throughput(Throughput::Elements(1000));

        // Pre-populate bitmap
        let mut smol = SmolBitmap::new();
        let mut bv = BitVec::<u64, Lsb0>::new();
        bv.resize(size, false);

        for i in (0..size).step_by(3) {
            smol.insert(i);
            bv.insert(i, true);
        }

        let test_indices: Vec<usize> = (0..1000).map(|i| i % size).collect();

        group.bench_with_input(
            BenchmarkId::new("SmolBitmap", size),
            &(&smol, &test_indices),
            |b, (bitmap, indices)| {
                b.iter(|| {
                    let mut sum = 0;
                    for &i in *indices {
                        if bitmap.get(i) {
                            sum += 1;
                        }
                    }
                    black_box(sum);
                });
            },
        );

        group.bench_with_input(
            BenchmarkId::new("BitVec", size),
            &(&bv, &test_indices),
            |b, (bitvec, indices)| {
                b.iter(|| {
                    let mut sum = 0;
                    for &i in *indices {
                        if bitvec[i] {
                            sum += 1;
                        }
                    }
                    black_box(sum);
                });
            },
        );
    }

    group.finish();
}

fn bench_iteration(c: &mut Criterion) {
    let mut group = c.benchmark_group("iteration");

    for &size in &[100, 1000, 10000] {
        // Create sparse bitmaps
        let mut smol = SmolBitmap::new();
        let mut bv = BitVec::<u64, Lsb0>::new();
        bv.resize(size, false);

        // Set every 10th bit
        for i in (0..size).step_by(10) {
            smol.insert(i);
            bv.insert(i, true);
        }

        group.throughput(Throughput::Elements((size / 10) as u64));

        group.bench_with_input(BenchmarkId::new("SmolBitmap", size), &smol, |b, bitmap| {
            b.iter(|| {
                let sum: usize = bitmap.iter().sum();
                black_box(sum);
            });
        });

        group.bench_with_input(BenchmarkId::new("BitVec", size), &bv, |b, bitvec| {
            b.iter(|| {
                let sum: usize = bitvec.iter_ones().sum();
                black_box(sum);
            });
        });
    }

    group.finish();
}

fn bench_count_ones(c: &mut Criterion) {
    let mut group = c.benchmark_group("count_ones");

    for &size in &[100, 1000, 10000] {
        let mut smol = SmolBitmap::new();
        let mut bv = BitVec::<u64, Lsb0>::new();
        bv.resize(size, false);

        // Set 50% of bits
        for i in (0..size).step_by(2) {
            smol.insert(i);
            bv.insert(i, true);
        }

        group.bench_with_input(BenchmarkId::new("SmolBitmap", size), &smol, |b, bitmap| {
            b.iter(|| {
                let count = bitmap.count_ones();
                black_box(count);
            });
        });

        group.bench_with_input(BenchmarkId::new("BitVec", size), &bv, |b, bitvec| {
            b.iter(|| {
                let count = bitvec.count_ones();
                black_box(count);
            });
        });
    }

    group.finish();
}

criterion_group!(
    benches,
    bench_creation,
    bench_set_operations,
    bench_get_operations,
    bench_iteration,
    bench_count_ones,
);
criterion_main!(benches);
