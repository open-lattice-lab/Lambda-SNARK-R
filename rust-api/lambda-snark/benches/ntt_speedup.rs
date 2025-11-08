use criterion::{black_box, criterion_group, criterion_main, Criterion, BenchmarkId};
use lambda_snark::r1cs::R1CS;
use lambda_snark::sparse_matrix::SparseMatrix;
use lambda_snark_core::NTT_MODULUS;

/// Create R1CS for m constraints with multiplication gate pattern
fn create_r1cs_for_bench(m: usize, use_ntt_modulus: bool) -> (R1CS, Vec<u64>) {
    let n = m + 2; // m constraints + 1 (always) + 1 output
    let l = 1; // Only z[0]=1 is public
    
    // ALWAYS use NTT_MODULUS (2^64 - 2^32 + 1, prime)
    // Old modulus 17592186044417 = 17 × 1034834472613 (NOT prime)
    // Non-prime modulus breaks Lagrange interpolation at m=17+
    let modulus = NTT_MODULUS;
    
    // Create constraint pattern: z[i+1] * z[i+2] = z[0] for i=0..m-1
    // Using dense format for simplicity in benchmarks
    let mut a_dense = vec![vec![0u64; n]; m];
    let mut b_dense = vec![vec![0u64; n]; m];
    let mut c_dense = vec![vec![0u64; n]; m];
    
    for i in 0..m {
        a_dense[i][(i + 1) % n] = 1;
        b_dense[i][(i + 2) % n] = 1;
        c_dense[i][0] = 1; // z[0] = 1
    }
    
    let a = SparseMatrix::from_dense(&a_dense);
    let b = SparseMatrix::from_dense(&b_dense);
    let c = SparseMatrix::from_dense(&c_dense);
    
    let r1cs = R1CS::new(m, n, l, a, b, c, modulus);
    
    // Create witness that satisfies: z[i+1] * z[i+2] = 1
    let mut witness = vec![1u64]; // z[0] = 1
    for _ in 1..n {
        witness.push(1u64); // All z[i] = 1 satisfies constraints
    }
    
    (r1cs, witness)
}

/// Benchmark Lagrange interpolation (baseline O(m²))
fn bench_lagrange_baseline(c: &mut Criterion) {
    let mut group = c.benchmark_group("lagrange_baseline");
    
    for m in [16, 64, 256, 1024].iter() {
        let (r1cs, witness) = create_r1cs_for_bench(*m, false);
        
        group.bench_with_input(BenchmarkId::from_parameter(m), m, |b, _| {
            b.iter(|| {
                let _ = r1cs.compute_quotient_poly(black_box(&witness));
            });
        });
    }
    
    group.finish();
}

/// Benchmark NTT-optimized path (O(m log m))
#[cfg(feature = "fft-ntt")]
fn bench_ntt_optimized(c: &mut Criterion) {
    let mut group = c.benchmark_group("ntt_optimized");
    
    // Only power-of-2 sizes for NTT
    for m in [16, 64, 256, 1024, 4096].iter() {
        let (r1cs, witness) = create_r1cs_for_bench(*m, true);
        
        // Verify NTT will be used
        assert!(r1cs.should_use_ntt(), "NTT not enabled for m={}", m);
        
        group.bench_with_input(BenchmarkId::from_parameter(m), m, |b, _| {
            b.iter(|| {
                let _ = r1cs.compute_quotient_poly(black_box(&witness));
            });
        });
    }
    
    group.finish();
}

/// Benchmark comparison: Lagrange vs NTT for same m
#[cfg(feature = "fft-ntt")]
fn bench_speedup_comparison(c: &mut Criterion) {
    let mut group = c.benchmark_group("speedup_comparison");
    group.sample_size(10); // Fewer samples for large inputs
    
    for m in [16, 64, 256, 1024].iter() {
        // Baseline with non-NTT modulus
        let (r1cs_baseline, witness_baseline) = create_r1cs_for_bench(*m, false);
        group.bench_with_input(
            BenchmarkId::new("lagrange", m), 
            m, 
            |b, _| {
                b.iter(|| {
                    let _ = r1cs_baseline.compute_quotient_poly(black_box(&witness_baseline));
                });
            }
        );
        
        // NTT-optimized with NTT modulus
        let (r1cs_ntt, witness_ntt) = create_r1cs_for_bench(*m, true);
        assert!(r1cs_ntt.should_use_ntt(), "NTT not enabled for m={}", m);
        group.bench_with_input(
            BenchmarkId::new("ntt", m), 
            m, 
            |b, _| {
                b.iter(|| {
                    let _ = r1cs_ntt.compute_quotient_poly(black_box(&witness_ntt));
                });
            }
        );
    }
    
    group.finish();
}

#[cfg(not(feature = "fft-ntt"))]
fn bench_ntt_optimized(_c: &mut Criterion) {
    // NTT benchmarks disabled when feature is off
}

#[cfg(not(feature = "fft-ntt"))]
fn bench_speedup_comparison(_c: &mut Criterion) {
    // NTT comparison disabled when feature is off
}

criterion_group!(
    benches,
    bench_lagrange_baseline,
    bench_ntt_optimized,
    bench_speedup_comparison
);
criterion_main!(benches);
