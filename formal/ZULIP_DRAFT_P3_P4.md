# Polynomial Division in Fields — API Question

**Status**: 🔍 POSTED TO ZULIP (awaiting response)  
**Date**: 2025-11-16  
**Context**: Formal verification of Lambda-SNARK-R cryptographic protocol

---

## Problem Statement

I need to prove polynomial division with remainder for polynomials over a field, specifically showing that the remainder's degree is strictly less than the divisor's degree (when remainder is nonzero).

### Current Code

```lean
import Mathlib

/-- Polynomial division: `f = q * g + r` with `deg(r) < deg(g)`. -/
theorem polynomial_division {F : Type*} [Field F]
    (f g : Polynomial F) (hg : g ≠ 0) :
    ∃! qr : Polynomial F × Polynomial F,
      f = qr.1 * g + qr.2 ∧ (qr.2 = 0 ∨ qr.2.natDegree < g.natDegree) := by
  classical
  refine ⟨(f / g, f % g), ?exist, ?uniq⟩
  · constructor
    · simpa [mul_comm] using (EuclideanDomain.div_add_mod f g).symm
    · by_cases h : f % g = 0
      · exact Or.inl h
      · right
        -- Need: (f % g).natDegree < g.natDegree when f % g ≠ 0
        sorry
  · intro ⟨q', r'⟩ ⟨hqr, hdeg⟩
    -- Need: uniqueness of quotient and remainder
    sorry
```

---

## Specific Questions

### Q1: Degree Bound for Remainder

**What is the correct Mathlib lemma** to prove `(f % g).natDegree < g.natDegree` when `f % g ≠ 0`?

I tried:
- ❌ `Polynomial.degree_mod_lt` — Unknown constant
- ⚠️ `Polynomial.degree_modByMonic_lt` — requires monic proof, but we have arbitrary `g`
- ❌ `EuclideanDomain.mod_lt` — type mismatch (expects `Nat`, not degree)

**Context**: Polynomials over fields form a Euclidean domain with degree as the norm. The Euclidean property guarantees `degree(f % g) < degree(g)`, but I cannot find the right API.

### Q2: Division Uniqueness

**What is the standard approach** to prove uniqueness of quotient and remainder in Mathlib?

Given:
- `f = q₁ * g + r₁` with `deg(r₁) < deg(g)` or `r₁ = 0`
- `f = q₂ * g + r₂` with `deg(r₂) < deg(g)` or `r₂ = 0`

Need to show: `q₁ = q₂` and `r₁ = r₂`

**Attempted approach**:
```lean
-- From f = q₁·g + r₁ = q₂·g + r₂, derive (q₁ - q₂)·g = r₂ - r₁
-- Since deg(r₂ - r₁) < deg(g) and g ≠ 0, must have q₁ - q₂ = 0
```

But I'm not sure how to formalize the degree argument cleanly.

---

## Minimal Working Example (MWE)

```lean
import Mathlib.Data.Polynomial.FieldDivision
import Mathlib.Data.Polynomial.Degree.Definitions

open Polynomial

theorem degree_mod_bound {F : Type*} [Field F] (f g : Polynomial F) (hg : g ≠ 0) (h : f % g ≠ 0) :
    (f % g).natDegree < g.natDegree := by
  -- Euclidean domain property guarantees this, but how to extract it?
  sorry

theorem div_mod_unique {F : Type*} [Field F] (f g q₁ q₂ r₁ r₂ : Polynomial F)
    (hg : g ≠ 0)
    (h₁ : f = q₁ * g + r₁) (hdeg₁ : r₁ = 0 ∨ r₁.natDegree < g.natDegree)
    (h₂ : f = q₂ * g + r₂) (hdeg₂ : r₂ = 0 ∨ r₂.natDegree < g.natDegree) :
    q₁ = q₂ ∧ r₁ = r₂ := by
  -- Standard uniqueness argument via degree contradiction
  sorry
```

---

## Related Code Context

This is part of formal verification for a SNARK protocol where we need:
1. Polynomial division by vanishing polynomial `Z_H(X) = ∏ᵢ (X - ωⁱ)`
2. Proof that remainder is zero iff polynomial vanishes on all roots
3. Quotient polynomial properties for constraint checking

Current progress: 67% of formal proofs complete (12/18 theorems), this is one of the remaining blockers.

---

## Request

Could someone point me to:
1. The correct Mathlib lemma(s) for degree bounds on polynomial mod
2. Standard patterns for division uniqueness proofs in Mathlib
3. Any relevant examples in the Mathlib codebase

Thank you! 🙏

---

## Notes for Future Implementation

Once solution is received:
- [ ] Implement `degree_mod_bound` using suggested lemma
- [ ] Implement `div_mod_unique` using suggested pattern
- [ ] Close P3 (existence) and P4 (uniqueness) in `LambdaSNARK/Polynomial.lean`
- [ ] Update VERIFICATION_PLAN.md with progress
- [ ] Test with `lake build` to ensure stability
