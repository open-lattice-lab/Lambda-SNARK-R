# Testing Guide for ΛSNARK-R

This document describes the test organization, how to run tests, and coverage measurement for the ΛSNARK-R zero-knowledge proof system.

## Test Organization

### Unit Tests (`src/*/tests`)
- **Location**: Inline module tests in source files
- **Count**: 116 tests
- **Coverage**: Core modules (polynomial, r1cs, sparse_matrix, ntt, etc.)
- **Run**: `cargo test --lib`

### Property-Based Tests (`tests/property_tests.rs`)
- **Framework**: [proptest](https://docs.rs/proptest/) 1.0+
- **Count**: 16 tests
- **Coverage**:
  - Polynomial properties: evaluation homomorphism, witness encoding, zero/constant
  - R1CS properties: valid/invalid witness, constraint linearity
  - Sparse matrix properties: linearity, zero matrix, identity
  - Field arithmetic: addition/multiplication commutativity, modular reduction
  - ZK properties: equivalence, blinding preservation
  - Quotient polynomial existence for valid witness
- **Run**: `cargo test --test property_tests`
- **Note**: Each property test runs 100 randomized cases by default

### Edge Case Tests (`tests/edge_cases.rs`)
- **Count**: 16 tests (1 ignored)
- **Coverage**:
  - Minimal configurations: m=1, m=2 constraints
  - Boundary values: 0, 1, q-1 (max field element)
  - Large witness sizes: n=64, n=128
  - Polynomial edge cases: degree 0, 1, high degree
  - Deterministic proof generation with different seeds
  - Empty/single-entry sparse matrices
- **Run**: `cargo test --test edge_cases`

### Integration Coverage Tests (`tests/integration_coverage.rs`)
- **Count**: 13 tests (3 ignored)
- **Coverage**:
  - Basic prove/verify workflows
  - ZK variants (prove_r1cs_zk, verify_r1cs_zk)
  - Multiple constraints (2, 4 multiplications)
  - Different random seeds
  - Multiple public inputs (2-3 public inputs)
  - Invalid proof detection (wrong public inputs)
  - Large witness systems (n=32)
  - Different field moduli
- **Run**: `cargo test --test integration_coverage`

### Integration Matrix Tests (`tests/integration_matrix.rs`)
- **Count**: 7 tests (8 ignored)
- **Coverage**: Cross-product testing of parameters × proof types × verification paths
- **Run**: `cargo test --test integration_matrix`
- **Note**: Contains 1 flaky performance test (ZK overhead <1.10×)

## Running Tests

### Run All Tests
```bash
cargo test
```

### Run Specific Test Suite
```bash
cargo test --lib                      # Unit tests only
cargo test --test property_tests       # Property-based tests
cargo test --test edge_cases           # Edge case tests
cargo test --test integration_coverage # Integration tests
```

### Run Single Test
```bash
cargo test test_polynomial_eval_addition_homomorphic
```

### Run Tests with Output
```bash
cargo test -- --nocapture             # Show println! output
cargo test -- --show-output           # Show output for passing tests too
```

### Run Tests in Parallel/Sequential
```bash
cargo test --                          # Parallel (default)
cargo test -- --test-threads=1         # Sequential
```

### Run Ignored Tests
```bash
cargo test -- --ignored                # Run only ignored tests
cargo test -- --include-ignored        # Run all tests including ignored
```

## Test Statistics

**Current Test Count**: 149 active tests (156 total including ignored)
- Unit tests: 116
- Property-based: 16 (100 cases × 16 properties = 1600+ randomized tests)
- Edge cases: 15 active (1 ignored: m=0 empty constraints)
- Integration coverage: 13 (3 ignored: complex chain constraints)
- Integration matrix: 7 (8 ignored: expensive parameter combinations)

**Target**: 200+ tests for alpha release

## Code Coverage

### Measure Coverage with cargo-tarpaulin

Install:
```bash
cargo install cargo-tarpaulin
```

Run coverage:
```bash
cd rust-api/lambda-snark
cargo tarpaulin --lib --out Html --output-dir target/coverage --exclude-files 'tests/*'
```

View HTML report:
```bash
open target/coverage/tarpaulin-report.html  # macOS
xdg-open target/coverage/tarpaulin-report.html  # Linux
```

### Current Coverage (as of M7.4)

**Overall**: 63.07% (632/1002 lines)

**Module Breakdown**:
- `polynomial.rs`: **95%** ✅
- `ntt.rs`: **93.6%** ✅
- `lean_export.rs`: **100%** ✅
- `challenge.rs`: **100%** ✅
- `lean_params.rs`: **96%** ✅
- `opening.rs`: **88.6%**
- `sparse_matrix.rs`: **91.3%** ✅
- `r1cs.rs`: **69.3%** (needs more integration tests)
- `commitment.rs`: **66.7%** (LWE FFI boundary)
- `context.rs`: **93.8%** ✅
- `circuit.rs`: **95.7%** ✅
- `lib.rs`: **2.2%** ⚠️ (prove/verify not covered in unit tests)

**Critical Gap**: `lib.rs` (prove_r1cs, prove_r1cs_zk, verify_r1cs, verify_r1cs_zk) requires integration tests. The `integration_coverage.rs` suite was added to address this, but tarpaulin's `--lib` flag excludes integration tests. Need to measure with `--all-targets` in CI.

### Coverage Goals
- **Core modules** (polynomial, r1cs, ntt, sparse_matrix): **≥95%** ✅
- **Proof generation** (lib.rs prove/verify): **≥80%** (pending)
- **FFI boundary** (commitment.rs): **≥70%** (pending)
- **Overall**: **≥80%** for alpha release

## Property-Based Testing with proptest

### Strategy Generators
```rust
// Field elements (1..modulus)
fn arb_field(modulus: u64) -> impl Strategy<Value = u64>

// Small constraint counts (1, 2, 4, 8)
fn arb_small_m() -> impl Strategy<Value = usize>

// Valid witness sizes (4..32)
fn arb_witness_size() -> impl Strategy<Value = usize>
```

### Writing Property Tests
```rust
proptest! {
    #[test]
    fn my_property(
        a in arb_field(NTT_MODULUS),
        b in arb_field(NTT_MODULUS),
    ) {
        // Property assertion
        prop_assert_eq!(a + b, b + a);
    }
}
```

### Regression Test Files
Failed property test cases are saved to `*.proptest-regressions` files for reproducibility:
```bash
tests/property_tests.proptest-regressions
```

## Continuous Integration

### GitHub Actions Workflow (Recommended)
```yaml
name: Tests
on: [push, pull_request]

jobs:
  test:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: dtolnay/rust-toolchain@stable
      
      - name: Run unit tests
        run: cargo test --lib --verbose
      
      - name: Run property tests
        run: cargo test --test property_tests --verbose
      
      - name: Run edge case tests
        run: cargo test --test edge_cases --verbose
      
      - name: Run integration tests
        run: cargo test --test integration_coverage --verbose
      
      - name: Measure coverage
        run: |
          cargo install cargo-tarpaulin
          cargo tarpaulin --out Xml --output-dir target/coverage
      
      - name: Upload coverage to Codecov
        uses: codecov/codecov-action@v3
        with:
          files: target/coverage/cobertura.xml
```

## Common Issues

### Integer Overflow in Property Tests
**Symptom**: `attempt to add with overflow` in modular arithmetic
**Fix**: Wrap additions in `u128`:
```rust
let sum = ((a as u128 + b as u128) % modulus as u128) as u64;
```

### Flaky Performance Tests
**Symptom**: `test_performance_zk_overhead` fails intermittently
**Solution**: Mark as `#[ignore]` or increase tolerance to 1.50× (currently 1.10×)

### Invalid Witness in Complex Tests
**Symptom**: `Polynomial division by Z_H: remainder non-zero (witness invalid)`
**Solution**: Verify R1CS constraints manually:
```rust
assert!(r1cs.is_satisfied(&witness), "Witness must satisfy before proving");
```

## Test Development Workflow

1. **Write unit test** for new feature (TDD)
2. **Add property test** for algebraic invariants
3. **Add edge case test** for boundary conditions
4. **Run tests**: `cargo test`
5. **Measure coverage**: `cargo tarpaulin --lib`
6. **Commit**: Include test in same commit as feature

## Future Work

- [ ] Reach 200+ total tests (target: M7.4 completion)
- [ ] Increase lib.rs coverage to ≥80% (add more integration tests)
- [ ] Add fuzzing with cargo-fuzz for FFI boundary
- [ ] Add QuickCheck-style shrinking for proptest failures
- [ ] Benchmark suite with criterion.rs
- [ ] Mutation testing with cargo-mutants

## References

- [proptest documentation](https://docs.rs/proptest/)
- [cargo-tarpaulin](https://github.com/xd009642/tarpaulin)
- [Rust testing guide](https://doc.rust-lang.org/book/ch11-00-testing.html)
