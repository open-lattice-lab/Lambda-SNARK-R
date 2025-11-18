/-
  Auxiliary results relating quotient polynomials and R1CS satisfaction.
  Extracted from Soundness development so both ForkingInfrastructure and
  Soundness can rely on the same lemmas without cyclic imports.
-/

import LambdaSNARK.Core
import LambdaSNARK.Polynomial

namespace LambdaSNARK

open Polynomial

/-- Quotient polynomial exists iff witness satisfies R1CS. -/
@[simp] theorem quotient_exists_iff_satisfies {F : Type} [Field F] [DecidableEq F]
    (cs : R1CS F) (z : Witness F cs.nVars) (m : ℕ) (ω : F)
    (h_m : m = cs.nCons) (hω : IsPrimitiveRoot ω m) :
    satisfies cs z ↔
    ∃ (f : Polynomial F),
      (∀ i : Fin cs.nCons, f.eval (ω ^ (i : ℕ)) = constraintPoly cs z i) ∧
      f %ₘ vanishing_poly m ω = 0 :=
by
  constructor
  · intro h_sat
    refine ⟨0, ?_, ?_⟩
    · intro i
      have h_zero := (satisfies_iff_constraint_zero cs z).mp h_sat i
      simp [h_zero]  -- constraint polynomial vanishes at every index
    · simp [Polynomial.zero_modByMonic]
  · intro h
    rcases h with ⟨f, hf_eval, hf_mod⟩
    refine (satisfies_iff_constraint_zero cs z).mpr ?_
    intro i
    have h_van := (remainder_zero_iff_vanishing f m ω hω).mp hf_mod
    obtain ⟨j, hj⟩ : ∃ j : Fin m, (j : ℕ) = (i : ℕ) :=
      ⟨⟨i, h_m ▸ i.isLt⟩, rfl⟩
    calc
      constraintPoly cs z i
          = f.eval (ω ^ (i : ℕ)) := (hf_eval i).symm
      _ = f.eval (ω ^ (j : ℕ)) := by simp [hj]
      _ = 0 := h_van j

end LambdaSNARK
