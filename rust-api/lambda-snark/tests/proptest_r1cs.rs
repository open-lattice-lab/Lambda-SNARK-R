//! Property-based tests for ΛSNARK-R using proptest.
//!
//! Tests algebraic invariants, edge cases, and randomized scenarios across:
//! - R1CS constraint satisfaction
//! - Polynomial operations (addition, evaluation)
//! - NTT transformations (if fft-ntt feature enabled)
//!
//! Each property runs 1000 random test cases by default.

use proptest::prelude::*;
use lambda_snark::r1cs::R1CS;
use lambda_snark::sparse_matrix::SparseMatrix;
use lambda_snark::polynomial::Polynomial;

/// Modulus for testing (2^64 - 2^32 + 1, NTT-friendly)
/// Use NTT_MODULUS for NTT tests, LEGACY_MODULUS for non-NTT tests
const TEST_MODULUS: u64 = 17592186044417;  // Legacy 44-bit for R1CS tests

// ============================================================================
// R1CS Properties
// ============================================================================

/// Helper: Create simple R1CS for multiplication gate: a * b = c
/// Witness: z = [1, a, b, c]
/// Constraint: (0*z[0] + 1*z[1]) * (0*z[0] + 0*z[1] + 1*z[2]) = (0*z[0] + 0*z[1] + 0*z[2] + 1*z[3])
fn create_multiplication_r1cs(modulus: u64) -> R1CS {
    // A matrix: selects z[1] (coefficient a)
    // Row 0: [0, 1, 0, 0]
    let a_matrix = SparseMatrix::from_dense(&vec![vec![0, 1, 0, 0]]);
    
    // B matrix: selects z[2] (coefficient b)
    // Row 0: [0, 0, 1, 0]
    let b_matrix = SparseMatrix::from_dense(&vec![vec![0, 0, 1, 0]]);
    
    // C matrix: selects z[3] (coefficient c)
    // Row 0: [0, 0, 0, 1]
    let c_matrix = SparseMatrix::from_dense(&vec![vec![0, 0, 0, 1]]);
    
    R1CS::new(1, 4, 2, a_matrix, b_matrix, c_matrix, modulus)
}

proptest! {
    /// Property 1: Valid witness satisfies R1CS constraints
    ///
    /// For multiplication gate a * b = c:
    /// - Witness [1, a, b, a*b mod q] MUST satisfy
    /// - Witness [1, a, b, wrong_c] MUST NOT satisfy
    #[test]
    fn prop_valid_witness_satisfies_r1cs(
        a in 0u64..1000,
        b in 0u64..1000,
    ) {
        let r1cs = create_multiplication_r1cs(TEST_MODULUS);
        
        // Valid witness: c = a * b mod q
        let c_correct = ((a as u128 * b as u128) % TEST_MODULUS as u128) as u64;
        let witness_valid = vec![1, a, b, c_correct];
        
        prop_assert!(
            r1cs.is_satisfied(&witness_valid),
            "Valid witness [1, {}, {}, {}] should satisfy R1CS",
            a, b, c_correct
        );
        
        // Invalid witness: c = a * b + 1 (wrong)
        let c_wrong = (c_correct + 1) % TEST_MODULUS;
        let witness_invalid = vec![1, a, b, c_wrong];
        
        prop_assert!(
            !r1cs.is_satisfied(&witness_invalid),
            "Invalid witness [1, {}, {}, {}] should NOT satisfy R1CS",
            a, b, c_wrong
        );
    }
    
    /// Property 2: Constraint evaluation is deterministic
    ///
    /// Multiple evaluations of same witness produce same result.
    #[test]
    fn prop_r1cs_eval_deterministic(
        a in 0u64..1000,
        b in 0u64..1000,
    ) {
        let r1cs = create_multiplication_r1cs(TEST_MODULUS);
        let c = ((a as u128 * b as u128) % TEST_MODULUS as u128) as u64;
        let witness = vec![1, a, b, c];
        
        let eval1 = r1cs.is_satisfied(&witness);
        let eval2 = r1cs.is_satisfied(&witness);
        let eval3 = r1cs.is_satisfied(&witness);
        
        prop_assert_eq!(eval1, eval2);
        prop_assert_eq!(eval2, eval3);
    }
    
    /// Property 3: Public input extraction is stable
    ///
    /// Public inputs (z[0..l]) are deterministically extracted.
    #[test]
    fn prop_public_inputs_stable(
        a in 0u64..1000,
        b in 0u64..1000,
    ) {
        let r1cs = create_multiplication_r1cs(TEST_MODULUS);
        let c = ((a as u128 * b as u128) % TEST_MODULUS as u128) as u64;
        let witness = vec![1, a, b, c];
        
        // R1CS has l=2 public inputs: z[0], z[1]
        let public1 = r1cs.public_inputs(&witness);
        let public2 = r1cs.public_inputs(&witness);
        
        prop_assert_eq!(public1, public2);
        prop_assert_eq!(public1.len(), 2);
        prop_assert_eq!(public1[0], 1);
        prop_assert_eq!(public1[1], a);
    }
}

// ============================================================================
// Polynomial Properties
// ============================================================================

proptest! {
    /// Property 4: Polynomial addition is commutative
    ///
    /// For all polynomials f, g: f + g = g + f
    #[test]
    fn prop_poly_add_commutative(
        coeffs_a in prop::collection::vec(0u64..1000, 1..20),
        coeffs_b in prop::collection::vec(0u64..1000, 1..20),
    ) {
        let f = Polynomial::from_witness(&coeffs_a, TEST_MODULUS);
        let g = Polynomial::from_witness(&coeffs_b, TEST_MODULUS);
        
        let f_plus_g = f.add(&g);
        let g_plus_f = g.add(&f);
        
        // Check coefficients match
        let max_deg = f.degree().max(g.degree());
        for i in 0..=max_deg {
            let coeff_fg = f_plus_g.coeff(i).map(|c| c.value()).unwrap_or(0);
            let coeff_gf = g_plus_f.coeff(i).map(|c| c.value()).unwrap_or(0);
            
            prop_assert_eq!(
                coeff_fg, coeff_gf,
                "Coefficient mismatch at index {}: {} != {}",
                i, coeff_fg, coeff_gf
            );
        }
    }
    
    /// Property 5: Polynomial addition preserves degree bound
    ///
    /// For polynomials f, g: deg(f + g) ≤ max(deg(f), deg(g))
    #[test]
    fn prop_poly_add_degree_bound(
        coeffs_a in prop::collection::vec(0u64..1000, 1..30),
        coeffs_b in prop::collection::vec(0u64..1000, 1..30),
    ) {
        let f = Polynomial::from_witness(&coeffs_a, TEST_MODULUS);
        let g = Polynomial::from_witness(&coeffs_b, TEST_MODULUS);
        
        let sum = f.add(&g);
        let expected_max_deg = f.degree().max(g.degree());
        
        prop_assert!(
            sum.degree() <= expected_max_deg,
            "Degree bound violated: deg({}) = {} > max({}, {}) = {}",
            "f+g", sum.degree(), f.degree(), g.degree(), expected_max_deg
        );
    }
    
    /// Property 6: Polynomial evaluation consistency
    ///
    /// Evaluating at same point produces same result.
    #[test]
    fn prop_poly_eval_consistent(
        coeffs in prop::collection::vec(0u64..1000, 1..20),
        alpha in 0u64..100,
    ) {
        let f = Polynomial::from_witness(&coeffs, TEST_MODULUS);
        
        use lambda_snark_core::Field;
        let alpha_field = Field::new(alpha);
        
        let eval1 = f.evaluate(alpha_field);
        let eval2 = f.evaluate(alpha_field);
        let eval3 = f.evaluate(alpha_field);
        
        prop_assert_eq!(eval1.value(), eval2.value());
        prop_assert_eq!(eval2.value(), eval3.value());
    }
    
    /// Property 7: Polynomial from witness preserves length
    ///
    /// Encoding witness as polynomial preserves number of coefficients.
    #[test]
    fn prop_poly_from_witness_length(
        witness in prop::collection::vec(0u64..10000, 1..100),
    ) {
        let f = Polynomial::from_witness(&witness, TEST_MODULUS);
        
        prop_assert_eq!(
            f.len(), witness.len(),
            "Polynomial length {} != witness length {}",
            f.len(), witness.len()
        );
    }
    
    /// Property 8: Zero polynomial properties
    ///
    /// f(X) + 0 = f(X) and 0.eval(α) = 0 for all α.
    #[test]
    fn prop_zero_poly_identity(
        coeffs in prop::collection::vec(0u64..1000, 1..20),
        alpha in 0u64..100,
    ) {
        use lambda_snark_core::Field;
        
        let f = Polynomial::from_witness(&coeffs, TEST_MODULUS);
        let zero = Polynomial::from_witness(&[0], TEST_MODULUS);
        
        // f + 0 = f
        let f_plus_zero = f.add(&zero);
        prop_assert_eq!(f_plus_zero.degree(), f.degree());
        
        // 0(α) = 0 for all α
        let alpha_field = Field::new(alpha);
        prop_assert_eq!(zero.evaluate(alpha_field).value(), 0);
    }
}

// ============================================================================
// NTT Properties (feature-gated)
// ============================================================================

#[cfg(feature = "fft-ntt")]
mod ntt_properties {
    use super::*;
    use lambda_snark::r1cs::{vanishing_poly, poly_add};
    use lambda_snark_core::{NTT_MODULUS, NTT_PRIMITIVE_ROOT};
    
    proptest! {
        /// Property 9: Vanishing polynomial Z_H(ω^i) = 0 for domain points
        ///
        /// For NTT domain H = {ω^0, ω^1, ..., ω^{m-1}}, the vanishing polynomial
        /// Z_H(X) = X^m - 1 must evaluate to zero at all domain points.
        #[test]
        fn prop_vanishing_poly_zeros_at_domain(
            m_log2 in prop::sample::select(&[4u32, 5, 6, 7, 8]), // m = 16, 32, 64, 128, 256
        ) {
            let m = 1usize << m_log2; // 2^m_log2
            
            // Use NTT_MODULUS for NTT tests (64-bit, has 2^32-th roots)
            let z_h = vanishing_poly(m, NTT_MODULUS, true);
            
            // Get root of unity ω for domain size m
            use lambda_snark::ntt::compute_root_of_unity;
            let omega = compute_root_of_unity(m, NTT_MODULUS, NTT_PRIMITIVE_ROOT);
            
            // Check Z_H(ω^i) = 0 for i = 0..m
            for i in 0..m {
                let omega_i = mod_pow(omega, i as u64, NTT_MODULUS);
                let eval = eval_poly(&z_h, omega_i, NTT_MODULUS);
                
                prop_assert_eq!(
                    eval, 0,
                    "Z_H(ω^{}) = {} ≠ 0 (m={}, ω={})",
                    i, eval, m, omega
                );
            }
        }
        
        /// Property 10: Polynomial addition modular properties
        ///
        /// (f + g)(α) = f(α) + g(α) mod q
        #[test]
        fn prop_poly_add_eval_homomorphism(
            coeffs_a in prop::collection::vec(0u64..1000, 1..20),
            coeffs_b in prop::collection::vec(0u64..1000, 1..20),
            alpha in 0u64..100,
        ) {
            // Use NTT_MODULUS for consistency with vanishing poly tests
            let sum_poly = poly_add(&coeffs_a, &coeffs_b, NTT_MODULUS);
            
            let eval_sum = eval_poly(&sum_poly, alpha, NTT_MODULUS);
            let eval_a = eval_poly(&coeffs_a, alpha, NTT_MODULUS);
            let eval_b = eval_poly(&coeffs_b, alpha, NTT_MODULUS);
            
            // Use u128 to avoid overflow when adding near-modulus values
            let sum_evals = ((eval_a as u128 + eval_b as u128) % NTT_MODULUS as u128) as u64;
            
            prop_assert_eq!(
                eval_sum, sum_evals,
                "(f+g)({}) = {} ≠ f({}) + g({}) mod q = {}",
                alpha, eval_sum, alpha, alpha, sum_evals
            );
        }
    }
    
    /// Helper: Modular exponentiation
    fn mod_pow(base: u64, mut exp: u64, modulus: u64) -> u64 {
        let mut result = 1u128;
        let mut b = (base % modulus) as u128;
        let m = modulus as u128;
        
        while exp > 0 {
            if exp & 1 == 1 {
                result = (result * b) % m;
            }
            b = (b * b) % m;
            exp >>= 1;
        }
        
        result as u64
    }
    
    /// Helper: Evaluate polynomial at point
    fn eval_poly(coeffs: &[u64], x: u64, modulus: u64) -> u64 {
        let mut result = 0u128;
        let mut x_pow = 1u128;
        let m = modulus as u128;
        
        for &coeff in coeffs {
            result = (result + (coeff as u128 * x_pow) % m) % m;
            x_pow = (x_pow * x as u128) % m;
        }
        
        result as u64
    }
}

// ============================================================================
// Test Configuration
// ============================================================================

// Run all property tests:
// ```bash
// cargo test --test proptest_r1cs
// ```
//
// Run with more cases (stress test):
// ```bash
// PROPTEST_CASES=10000 cargo test --test proptest_r1cs
// ```
//
// Run with verbose output:
// ```bash
// cargo test --test proptest_r1cs -- --nocapture
// ```
