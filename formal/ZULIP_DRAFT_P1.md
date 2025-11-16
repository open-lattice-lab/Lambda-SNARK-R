# Zulip Draft: IsPrimitiveRoot.ne_zero Usage Pattern

**Stream**: `#mathlib`  
**Topic**: Extracting `ω ≠ 0` from `IsPrimitiveRoot ω m`  
**Status**: ✅ **RESOLVED** — Solution received from Lean community

---

## Solution Summary

**TL;DR**: You cannot get `ω ≠ 0` from `IsPrimitiveRoot ω m` without proving `m ≠ 0` first. The idiomatic pattern is:

```lean
have hm : m ≠ 0 := (Nat.zero_lt_of_lt hi).ne'  -- derive from i < m
have hω0 : ω ≠ 0 := h_root.ne_zero hm
```

**Better approach**: Use `IsPrimitiveRoot.pow_eq_one_iff_dvd` directly to avoid needing `ω ≠ 0`:

```lean
-- From ω^i = ω^j, derive ω^(j-i) = 1, hence m ∣ (j-i)
-- With i,j < m, this forces j-i = 0, so i = j
have hmdiv : m ∣ (j - i) := (h_root.pow_eq_one_iff_dvd _).mp hpow
```

---

## Original Problem (ARCHIVED)

## Context

I'm formalizing a SNARK verification system in Lean 4 and need to prove injectivity of powers of a primitive root. I'm hitting a type mismatch when trying to extract `ω ≠ 0` from `IsPrimitiveRoot ω m`.

## Problem

The lemma `IsPrimitiveRoot.ne_zero` has signature:
```lean
theorem IsPrimitiveRoot.ne_zero {M : Type u_1} [CommMonoid M] [Nontrivial M] {ζ : M} {n : ℕ} 
  (h : IsPrimitiveRoot ζ n) (hn : n ≠ 0) : ζ ≠ 0
```

But in my proof context, I have:
- `h_root : IsPrimitiveRoot ω m` (primitive root hypothesis)
- **Goal**: `ω ≠ 0` (directly, without extra `m ≠ 0` proof)

When I try `have hω0 := h_root.ne_zero`, I get:
```
type mismatch
  h_root.ne_zero
has type
  ?m.11302 ≠ 0 → ω ≠ 0 : Prop
but is expected to have type
  ω ≠ 0 : Prop
```

## Minimal Working Example

```lean
import Mathlib.NumberTheory.RootsOfUnity.Basic
import Mathlib.Algebra.Ring.Defs

theorem primitive_root_pow_injective {F : Type} [Field F]
    (m : ℕ) (ω : F) (h_root : IsPrimitiveRoot ω m)
    (i j : ℕ) (hi : i < m) (hj : j < m)
    (h_eq : ω ^ i = ω ^ j) :
    i = j := by
  -- Want to show: ω ≠ 0 (needed for mul_left_cancel₀)
  -- have hω0 : ω ≠ 0 := h_root.ne_zero  -- TYPE ERROR
  sorry
```

## Question

What's the idiomatic way to extract `ω ≠ 0` from `IsPrimitiveRoot ω m` in this context?

**Options I've considered**:
1. Provide explicit `m ≠ 0` proof: `h_root.ne_zero (Nat.pos_of_ne_zero ...)`
   - But `m` might be 0 in some degenerate cases?
2. Use `IsPrimitiveRoot.ne_one` instead?
3. Some instance/coercion I'm missing?

**Expected workflow**: Since primitive roots are inherently nonzero (by definition), I'd expect a direct path `IsPrimitiveRoot ω m → ω ≠ 0` without case-splitting on `m`.

## Additional Context

- Lean 4.15.0 with latest Mathlib4
- Field context (so division is available)
- Target theorem is proving `ω^i = ω^j → i = j` for `0 ≤ i, j < m`

---

## Implementation Patterns

### Pattern 1: Derive `m ≠ 0` from bounds

```lean
theorem primitive_root_pow_injective {F : Type*} [Field F]
    (m : ℕ) (ω : F) (h_root : IsPrimitiveRoot ω m)
    (i j : ℕ) (hi : i < m) (hj : j < m)
    (h_eq : ω ^ i = ω ^ j) :
    i = j := by
  -- Derive m ≠ 0 from i < m
  have hm_pos : 0 < m := Nat.zero_lt_of_lt hi
  have hm : m ≠ 0 := hm_pos.ne'
  have hω0 : ω ≠ 0 := h_root.ne_zero hm
  -- ... rest of proof
```

### Pattern 2: Use `pow_eq_one_iff_dvd` (preferred)

```lean
theorem primitive_root_pow_injective {F : Type*} [Field F]
    (m : ℕ) (ω : F) (h_root : IsPrimitiveRoot ω m)
    (i j : ℕ) (hi : i < m) (hj : j < m)
    (h_eq : ω ^ i = ω ^ j) :
    i = j := by
  wlog hij : i ≤ j generalizing i j
  · exact (this m ω h_root j i hj hi h_eq.symm (le_of_not_le hij)).symm
  -- From ω^i = ω^j, derive ω^(j-i) = 1
  have hpow : ω ^ (j - i) = 1 := by
    -- Rearrange using pow_add and field arithmetic
    sorry  -- details: field cancellation
  -- Use primitivity: ω^k = 1 ↔ m ∣ k
  have hm_pos : 0 < m := Nat.zero_lt_of_lt hi
  have hmdiv : m ∣ (j - i) := (h_root.pow_eq_one_iff_dvd _).mp hpow
  -- But j - i < m, so j - i = 0
  have : j - i = 0 := by
    have hjmi_lt : j - i < m := Nat.sub_lt_of_pos_le hm_pos hij
    exact Nat.eq_of_dvd_of_lt hm_pos hmdiv hjmi_lt
  exact Nat.sub_eq_zero.mp this
```

### Pattern 3: Use `Fin m` indices

```lean
-- If using Fin m directly, m ≠ 0 is automatic:
theorem primitive_root_pow_injective_fin {F : Type*} [Field F]
    (m : ℕ) (ω : F) (h_root : IsPrimitiveRoot ω m)
    (i j : Fin m) (h_eq : ω ^ (i : ℕ) = ω ^ (j : ℕ)) :
    i = j := by
  -- Fin m nonempty implies 0 < m
  have hm_pos : 0 < m := by
    have : 0 < Fintype.card (Fin m) := Fintype.card_pos_iff.mpr ⟨i⟩
    simpa [Fintype.card_fin] using this
  -- ... rest of proof
```

---

## Key Insights from Community

1. **Why `m ≠ 0` is required**: `IsPrimitiveRoot.ne_zero` rules out the degenerate "order 0" case
2. **Preferred approach**: Use `pow_eq_one_iff_dvd` API instead of explicit cancellation
3. **Common mistake**: Trying to extract `ω ≠ 0` without first proving `m ≠ 0`
4. **Idiomatic pattern**: Derive `m ≠ 0` from existing bounds (`i < m`, `i : Fin m`, etc.)

---

## Action Items

- [x] Received solution from Lean community
- [ ] Implement Pattern 2 (`pow_eq_one_iff_dvd`) for P1
- [ ] Update Polynomial.lean with working proof
- [ ] Document pattern in VERIFICATION_PLAN.md

---

## References

- Mathlib: `Mathlib.NumberTheory.RootsOfUnity.Basic`
- Key lemma: `IsPrimitiveRoot.pow_eq_one_iff_dvd`
- Alternative: `IsPrimitiveRoot.ne_zero` with explicit `m ≠ 0`

**Last Updated**: 2025-11-16  
**Status**: Ready for implementation
<!--  -->