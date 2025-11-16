# Zulip Draft: IsPrimitiveRoot.ne_zero Usage Pattern

**Stream**: `#mathlib`  
**Topic**: Extracting `ω ≠ 0` from `IsPrimitiveRoot ω m`

---

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

Any guidance on the right API usage pattern here would be appreciated!

---

## Related Code Context

Full proof attempt: https://github.com/SafeAGI-lab/Lambda-SNARK-R/blob/main/formal/LambdaSNARK/Polynomial.lean#L65-L72

Verification plan: https://github.com/SafeAGI-lab/Lambda-SNARK-R/blob/main/formal/VERIFICATION_PLAN.md
<!--  -->