use criterion::{BenchmarkId, Criterion, criterion_group, criterion_main};
use smol_bitmap::SmolBitmap;
use std::{collections::HashSet, hint::black_box};

fn bench_set_operations(c: &mut Criterion) {
    let mut group = c.benchmark_group("set_operations");

    // Benchmark setting bits in inline storage
    group.bench_function("set_inline", |b| {
        let mut bitmap = SmolBitmap::new();
        let mut i = 0;
        b.iter(|| {
            bitmap.set(i % 127, black_box(true));
            i += 1;
        });
    });

    // Benchmark setting bits in spilled storage
    group.bench_function("set_spilled", |b| {
        let mut bitmap = SmolBitmap::new();
        bitmap.insert(200); // Force spill
        let mut i = 0;
        b.iter(|| {
            bitmap.set(i % 500, black_box(true));
            i += 1;
        });
    });

    // Benchmark getting bits from inline storage
    group.bench_function("get_inline", |b| {
        let mut bitmap = SmolBitmap::new();
        for i in 0..100 {
            bitmap.insert(i);
        }
        let mut i = 0;
        b.iter(|| {
            black_box(bitmap.get(i % 100));
            i += 1;
        });
    });

    // Benchmark getting bits from spilled storage
    group.bench_function("get_spilled", |b| {
        let mut bitmap = SmolBitmap::new();
        for i in 0usize..500 {
            if i.is_multiple_of(2) {
                bitmap.insert(i);
            }
        }
        let mut i = 0;
        b.iter(|| {
            black_box(bitmap.get(i % 500));
            i += 1;
        });
    });

    group.finish();
}

fn bench_iteration(c: &mut Criterion) {
    let mut group = c.benchmark_group("iteration");

    for size in &[10, 50, 100, 500, 1000] {
        let mut bitmap = SmolBitmap::new();
        for i in (0..*size).step_by(2) {
            bitmap.insert(i);
        }

        group.bench_with_input(BenchmarkId::new("forward", size), &bitmap, |b, bitmap| {
            b.iter(|| {
                for bit in bitmap {
                    black_box(bit);
                }
            });
        });

        group.bench_with_input(BenchmarkId::new("reverse", size), &bitmap, |b, bitmap| {
            b.iter(|| {
                for bit in bitmap.iter().rev() {
                    black_box(bit);
                }
            });
        });
    }

    group.finish();
}

fn bench_set_operations_bulk(c: &mut Criterion) {
    let mut group = c.benchmark_group("bulk_operations");

    for size in &[10, 50, 100, 500] {
        let mut a = SmolBitmap::new();
        let mut b = SmolBitmap::new();

        for i in (0..*size).step_by(2) {
            a.insert(i);
        }
        for i in (0..*size).step_by(3) {
            b.insert(i);
        }

        group.bench_with_input(
            BenchmarkId::new("union", size),
            &(&a, &b),
            |bench, (a, b)| {
                bench.iter(|| {
                    black_box(a.union(b));
                });
            },
        );

        group.bench_with_input(
            BenchmarkId::new("intersection", size),
            &(&a, &b),
            |bench, (a, b)| {
                bench.iter(|| {
                    black_box(a.intersection(b));
                });
            },
        );

        group.bench_with_input(
            BenchmarkId::new("difference", size),
            &(&a, &b),
            |bench, (a, b)| {
                bench.iter(|| {
                    black_box(a.difference(b));
                });
            },
        );

        group.bench_with_input(
            BenchmarkId::new("symmetric_difference", size),
            &(&a, &b),
            |bench, (a, b)| {
                bench.iter(|| {
                    black_box(a.symmetric_difference(b));
                });
            },
        );
    }

    group.finish();
}

fn bench_from_iter(c: &mut Criterion) {
    let mut group = c.benchmark_group("from_iter");

    for size in &[10, 50, 100, 500, 1000] {
        let indices: Vec<usize> = (0..*size).step_by(2).collect();

        group.bench_with_input(
            BenchmarkId::new("smol_bitmap", size),
            &indices,
            |b, indices| {
                b.iter(|| {
                    let bitmap: SmolBitmap = indices.iter().copied().collect();
                    black_box(bitmap);
                });
            },
        );

        // Compare with HashSet for reference
        group.bench_with_input(BenchmarkId::new("hashset", size), &indices, |b, indices| {
            b.iter(|| {
                let set: HashSet<usize> = indices.iter().copied().collect();
                black_box(set);
            });
        });
    }

    group.finish();
}

fn bench_inline_vs_spilled_transition(c: &mut Criterion) {
    let mut group = c.benchmark_group("storage_transition");

    // Benchmark the cost of transitioning from inline to spilled
    group.bench_function("inline_to_spilled", |b| {
        b.iter(|| {
            let mut bitmap = SmolBitmap::new();
            // Fill up inline storage
            for i in 0..127 {
                bitmap.insert(i);
            }
            // This should trigger spill
            bitmap.insert(127);
            black_box(bitmap);
        });
    });

    // Benchmark shrink_to_fit
    group.bench_function("shrink_to_fit", |b| {
        b.iter(|| {
            let mut bitmap = SmolBitmap::new();
            // Force spill
            bitmap.insert(500);
            // Clear high bits
            bitmap.remove(500);
            // Set some low bits
            for i in 0..50 {
                bitmap.insert(i);
            }
            // Try to shrink back
            bitmap.shrink_to_fit();
            black_box(bitmap);
        });
    });

    group.finish();
}

fn bench_clone(c: &mut Criterion) {
    let mut group = c.benchmark_group("clone");

    // Clone inline bitmap
    let mut inline_bitmap = SmolBitmap::new();
    for i in 0..100 {
        inline_bitmap.insert(i);
    }

    group.bench_function("clone_inline", |b| {
        b.iter(|| {
            black_box(inline_bitmap.clone());
        });
    });

    // Clone spilled bitmap
    let mut spilled_bitmap = SmolBitmap::new();
    for i in 0usize..500 {
        if i.is_multiple_of(2) {
            spilled_bitmap.insert(i);
        }
    }

    group.bench_function("clone_spilled", |b| {
        b.iter(|| {
            black_box(spilled_bitmap.clone());
        });
    });

    group.finish();
}

criterion_group!(
    benches,
    bench_set_operations,
    bench_iteration,
    bench_set_operations_bulk,
    bench_from_iter,
    bench_inline_vs_spilled_transition,
    bench_clone,
);

criterion_main!(benches);
