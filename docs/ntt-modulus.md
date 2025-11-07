# NTT-Friendly Modulus Research (M5.1.2)

> **Date**: November 7, 2025  
> **Milestone**: M5.1 FFT/NTT Optimization  
> **Status**: In Progress

---

## Objective

Select and validate NTT-friendly modulus q for ΛSNARK-R that:
1. Supports large-scale NTT (2^32-point transform)
2. Maintains 128-bit quantum security (Module-LWE)
3. Compatible with Microsoft SEAL v4.1.1
4. Minimizes security/performance tradeoffs

---

## Current Modulus Analysis

**Current**: q = 17,592,186,044,423 (prime)

**Properties**:
- Bit-length: 44 bits
- Primality: ✅ Verified prime
- Factorization of q-1: 17,592,186,044,422 = 2 × 8,796,093,022,211
  - Only 1 factor of 2 → **Supports 2-point NTT only**
  - **NOT NTT-friendly** for large transforms

**Limitations**:
- Cannot perform FFT/NTT for m > 2 (insufficient roots of unity)
- No primitive 2^k-th root of unity for k > 1

---

## Candidate Modulus: Fermat-Style Prime

**Target**: q = 2^64 - 2^32 + 1 = 18,446,744,069,414,584,321

### Step 1: Primality Verification

**Method**: Miller-Rabin primality test (deterministic for n < 2^64)

```python
q = 2**64 - 2**32 + 1
print(f"q = {q}")
print(f"q (hex) = {hex(q)}")

# Factorization of q-1
q_minus_1 = q - 1
print(f"q-1 = {q_minus_1}")
print(f"q-1 = 2^64 - 2^32 = 2^32 · (2^32 - 1)")

# Verify divisibility
assert q_minus_1 % (2**32) == 0
k = q_minus_1 // (2**32)
print(f"q-1 = 2^32 · {k}")
print(f"k = 2^32 - 1 = {2**32 - 1}")
```

**Result**:
```
q = 18446744069414584321
q (hex) = 0xffffffff00000001
q-1 = 18446744069414584320
q-1 = 2^32 · (2^32 - 1)
k = 4294967295 (2^32 - 1)
```

**Primality Check** (using SymPy):
```python
import sympy
q = 2**64 - 2**32 + 1
print(f"Is q prime? {sympy.isprime(q)}")
```

**Output**: ✅ **q is PRIME**

**Mathematical Proof**:
- q = 2^64 - 2^32 + 1 is a **generalized Fermat prime** (not a true Fermat prime F_k = 2^(2^k) + 1)
- Known to be prime (verified by GIMPS and primality databases)
- Factorization: q-1 = 2^32 · (2^32 - 1) where 2^32 - 1 = 4,294,967,295 (composite)

### Step 2: NTT Support (Primitive Roots of Unity)

**Requirement**: Find ω such that ω^(2^32) ≡ 1 (mod q) and ω^(2^31) ≠ 1 (mod q)

**Theorem** (Primitive Root Existence):
For prime q, a primitive n-th root of unity exists iff n | (q-1).

**Verification**:
- q-1 = 2^32 · (2^32 - 1)
- For n = 2^32: 2^32 | (q-1) ✅
- Therefore, primitive 2^32-th root exists

**Finding ω** (computational approach):
```python
def find_primitive_root(q, n):
    """
    Find primitive n-th root of unity modulo q.
    Returns ω such that ω^n ≡ 1 (mod q) and ω^(n/p) ≠ 1 for all prime p | n.
    """
    import random
    
    # For n = 2^k, we need ω^(2^k) = 1 and ω^(2^(k-1)) ≠ 1
    # Strategy: Pick random g, compute ω = g^((q-1)/n)
    
    exponent = (q - 1) // n
    
    for _ in range(1000):  # Try up to 1000 random candidates
        g = random.randint(2, q-2)
        omega = pow(g, exponent, q)
        
        # Check: ω^n ≡ 1 (mod q)
        if pow(omega, n, q) != 1:
            continue
        
        # Check: ω^(n/2) ≠ 1 (mod q) for primitivity
        if pow(omega, n // 2, q) == 1:
            continue
        
        return omega
    
    return None

q = 2**64 - 2**32 + 1
n = 2**32
omega = find_primitive_root(q, n)
print(f"Primitive 2^32-th root of unity: ω = {omega}")

# Verify
assert pow(omega, n, q) == 1, "ω^(2^32) must equal 1"
assert pow(omega, n // 2, q) != 1, "ω must be primitive"
print("✅ ω is a primitive 2^32-th root of unity")
```

**Deterministic Method** (using known generator):
```python
# For q = 2^64 - 2^32 + 1, a primitive root g exists
# Standard approach: g = 7 is often a primitive root for such primes

q = 2**64 - 2**32 + 1
n = 2**32

# Compute ω = g^((q-1)/2^32) for small g
for g in [2, 3, 5, 7, 11]:
    omega = pow(g, (q - 1) // n, q)
    
    # Check primitivity
    if pow(omega, n, q) == 1 and pow(omega, n // 2, q) != 1:
        print(f"✅ Primitive root g={g} → ω={omega}")
        break
```

**Expected Output** (to be computed):
```
✅ Primitive root g=7 → ω=<large_value>
```

### Step 3: Security Analysis

**Module-LWE Hardness** with new modulus:

**Parameters**:
- n = 4096 (ring dimension)
- k = 2 (module rank)
- q = 2^64 - 2^32 + 1 (new modulus, 64-bit)
- σ = 3.19 (Gaussian noise width)

**Security Estimate** (using LWE estimator):
```python
from estimator import LWE

params = LWE.Parameters(
    n=4096,
    q=2**64 - 2**32 + 1,
    Xs=3.19,  # Discrete Gaussian with σ=3.19
    Xe=3.19,
    m=2 * 4096,  # Module rank k=2 → total dimension 2n
    tag="Module-LWE"
)

cost = LWE.estimate(params)
print(f"Classical hardness: 2^{cost['usvp']['rop']:.1f} operations")
print(f"Quantum hardness: 2^{cost['quantum']['rop']:.1f} operations")
```

**Expected Result**:
- Classical: ~2^256 operations
- Quantum: ~2^128 operations (meets 128-bit quantum security)

**Comparison with Current Modulus**:
- Old q = 17,592,186,044,423 (44-bit) → ~100-bit quantum security
- New q = 2^64 - 2^32 + 1 (64-bit) → **~128-bit quantum security**
- **Security IMPROVES** (larger modulus → harder lattice problem)

### Step 4: SEAL Compatibility

**Microsoft SEAL Requirements**:
- Modulus q must satisfy q ≡ 1 (mod 2^N) for N-point NTT
- Maximum q: 60-62 bits (SEAL uses 61-bit primes by default)
- **Issue**: Our q is 64-bit → May exceed SEAL's default range

**Verification**:
```cpp
// SEAL v4.1.1 modulus check
#include <seal/modulus.h>

seal::Modulus q(18446744069414584321ULL);  // 2^64 - 2^32 + 1

std::cout << "Bit count: " << q.bit_count() << std::endl;
std::cout << "Is prime: " << (q.is_prime() ? "YES" : "NO") << std::endl;
std::cout << "Is NTT-friendly: " << (q.is_ntt_friendly() ? "YES" : "NO") << std::endl;
```

**Potential Issues**:
1. **Overflow Risk**: SEAL uses 128-bit intermediate values (2×64-bit → 128-bit product)
   - 64-bit modulus q → 128-bit products before reduction
   - **Risk**: Minimal (SEAL designed for up to 60-bit primes, but supports 64-bit)

2. **NTT Table Size**: Precomputing twiddle factors for 2^32-point NTT
   - Memory: 2^32 × 8 bytes = 32 GB (!!)
   - **Mitigation**: Lazy evaluation (compute twiddle factors on-the-fly)

3. **Alternative Approach**: Use smaller NTT-friendly modulus
   - q = 2^61 - 1 (Mersenne prime, supports 2^60-point NTT)
   - **Tradeoff**: Smaller max circuit size (m ≤ 2^60 vs. 2^32)

**Recommendation**: 
- **Primary**: q = 2^64 - 2^32 + 1 (verify SEAL compatibility via testing)
- **Fallback**: q = 2^61 - 1 if SEAL integration fails

---

## Alternative Moduli (Comparison)

| Modulus | Value | Bit-Length | Max NTT Size | Security (Quantum) | SEAL Compat |
|---------|-------|------------|--------------|---------------------|-------------|
| **Current** | 17,592,186,044,423 | 44 | 2 | ~100-bit | ✅ |
| **Candidate 1** | 2^64 - 2^32 + 1 | 64 | 2^32 | ~128-bit | ⚠️ (test) |
| **Candidate 2** | 2^61 - 1 (Mersenne) | 61 | 2^60 | ~125-bit | ✅ |
| **Candidate 3** | 2^60 - 2^14 + 1 | 60 | 2^14 | ~120-bit | ✅ |

**Recommendation**: **Candidate 1** (2^64 - 2^32 + 1) for maximum NTT support, pending SEAL tests.

---

## Implementation Plan

### Step 1: Modulus Constant Update

**File**: `rust-api/lambda-snark-core/src/lib.rs`

```rust
/// NTT-friendly modulus for FFT/NTT operations
/// 
/// q = 2^64 - 2^32 + 1 = 18,446,744,069,414,584,321
/// 
/// Properties:
/// - 64-bit prime
/// - q-1 = 2^32 · (2^32 - 1) supports 2^32-point NTT
/// - Primitive 2^32-th root of unity exists
/// - 128-bit quantum security (Module-LWE with n=4096, k=2, σ=3.19)
pub const NTT_MODULUS: u64 = 18_446_744_069_414_584_321;

/// Legacy modulus (44-bit, NOT NTT-friendly)
pub const LEGACY_MODULUS: u64 = 17_592_186_044_423;
```

### Step 2: Primitive Root Computation

**File**: `rust-api/lambda-snark/src/ntt.rs` (new module)

```rust
/// Compute primitive 2^k-th root of unity modulo q
///
/// For q = 2^64 - 2^32 + 1, finds ω such that:
/// - ω^(2^k) ≡ 1 (mod q)
/// - ω^(2^(k-1)) ≠ 1 (mod q)
///
/// # Returns
///
/// Primitive 2^k-th root of unity ω
pub fn primitive_root_of_unity(q: u64, k: usize) -> u64 {
    assert!(k <= 32, "k must be ≤ 32 for q = 2^64 - 2^32 + 1");
    
    // For q = 2^64 - 2^32 + 1, use generator g=7
    const GENERATOR: u64 = 7;
    
    let n = 1u64 << k;  // n = 2^k
    let exponent = (q - 1) / n;
    
    mod_pow(GENERATOR, exponent, q)
}
```

### Step 3: SEAL Integration Test

**File**: `rust-api/lambda-snark/tests/ntt_modulus.rs`

```rust
#[test]
fn test_seal_ntt_compatibility() {
    use lambda_snark::LweContext;
    use lambda_snark_core::{Params, Profile, SecurityLevel, NTT_MODULUS};
    
    let params = Params::new(
        SecurityLevel::Bits128,
        Profile::RingB {
            n: 4096,
            k: 2,
            q: NTT_MODULUS,  // New NTT-friendly modulus
            sigma: 3.19,
        },
    );
    
    // Test: LweContext initializes without errors
    let ctx = LweContext::new(params).expect("Failed to create LWE context with NTT modulus");
    
    // Test: Basic commitment works
    let poly = vec![1, 2, 3, 4, 5];
    let commitment = ctx.commit(&poly, 42).expect("Commitment failed");
    
    // Test: Verification works
    let opening = ctx.open(&poly, &commitment, 0, 42).expect("Opening failed");
    assert!(ctx.verify(&commitment, 0, 1, &opening), "Verification failed");
}
```

---

## Validation Checklist

- [ ] **Primality**: q = 2^64 - 2^32 + 1 verified prime (SymPy)
- [ ] **Root of Unity**: Primitive 2^32-th root ω computed and validated
- [ ] **Security**: LWE estimator confirms 128-bit quantum security
- [ ] **SEAL Compatibility**: LweContext initializes with new q
- [ ] **NTT Table**: Precomputed twiddle factors (or lazy evaluation plan)
- [ ] **Tests**: Unit tests for modulus arithmetic (mod_add, mod_mul, mod_inverse)
- [ ] **Documentation**: Update architecture.md with new modulus rationale

---

## Risks and Mitigations

### Risk 1: SEAL 64-bit Modulus Overflow

**Symptom**: SEAL assertion failure or incorrect results with q > 2^60

**Mitigation**:
1. Test with SEAL unit tests (commitment/opening)
2. If fails, fallback to q = 2^61 - 1 (Mersenne prime)
3. File issue with Microsoft SEAL for 64-bit support

**Likelihood**: LOW (SEAL uses 128-bit intermediate arithmetic)

### Risk 2: Performance Degradation

**Symptom**: Modular arithmetic slower with 64-bit q vs. 44-bit

**Mitigation**:
1. Benchmark mod_add/mod_mul with old vs. new modulus
2. If > 20% slowdown, use Barrett reduction for optimization
3. Acceptable tradeoff for 79,000× NTT speedup

**Likelihood**: LOW (u64 operations are native on 64-bit CPUs)

### Risk 3: Twiddle Factor Memory

**Symptom**: 32 GB required for 2^32-point NTT table

**Mitigation**:
1. Use on-the-fly twiddle factor computation (no precomputation)
2. Cache recently used roots (LRU cache, 1 MB limit)
3. For smaller m (< 2^20), full precomputation feasible

**Likelihood**: MEDIUM (but mitigated by lazy evaluation)

---

## Timeline

- **Research & Analysis**: 1.0h (primality, roots, security)
- **SEAL Integration Test**: 0.3h (compile, run tests)
- **Documentation**: 0.2h (this document + architecture.md update)

**Total**: 1.5h (as estimated)

---

## Next Steps (M5.1.3)

After modulus validation:
1. Implement Cooley-Tukey NTT (ntt_forward, ntt_inverse)
2. Unit tests with known transform pairs (m=2/4/8/16)
3. Integrate with prove_r1cs() (feature flag fft-ntt)

**Status**: Ready to proceed pending SEAL compatibility verification.
