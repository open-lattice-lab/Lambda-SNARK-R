import LambdaSNARK.Soundness
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Polynomial.Basic

namespace LambdaSNARK.Tests

open LambdaSNARK

noncomputable section

/-- Simple vector commitment used to instantiate the probability lemmas in tests. -/
noncomputable def testVectorCommitment (F : Type) [CommRing F] : VectorCommitment F where
  PP := Unit
  Commitment := List F
  Opening := Unit
  setup _ := ()
  commit _ v _ := v
  openProof _ _ _ _ := ()
  verify _ _ _ _ _ := true
  binding := by
    intro _ v₁ v₂ _ _ h_ne h_commit
    exact h_ne (by simpa using h_commit)
  correctness := by intro _ _ _ _; simp

/-- Trivial adversary state with constant openings, adequate for exercising
`fork_success_bound`. -/
noncomputable def testAdversaryState {F : Type} [Field F] [DecidableEq F] :
    AdversaryState F (testVectorCommitment F) :=
  { randomness := 0
    pp := ()
    comm_Az := []
    comm_Bz := []
    comm_Cz := []
    comm_quotient := []
    quotient_poly := 0
    quotient_rand := 0
    quotient_commitment_spec := by
      simp [testVectorCommitment, Polynomial.coeffList_zero]
    domainSize := 1
    omega := 1
    respond := fun _ _ =>
      { Az_eval := 0
        Bz_eval := 0
        Cz_eval := 0
        quotient_eval := 0
        vanishing_eval := 0
        opening_Az_α := ()
        opening_Bz_β := ()
        opening_Cz_α := ()
        opening_quotient_α := () } }

private lemma fork_success_bound_zmod_univ
    {q : ℕ} [Fact (Nat.Prime q)] {ε : ℝ}
    (hε_pos : 0 < ε) (hε_le : ε ≤ 1) :
    1 ≥ ε ^ 2 / 2 - 1 / (q : ℝ) := by
  classical
  let VC := testVectorCommitment (ZMod q)
  let state := testAdversaryState (F := ZMod q)
  let valid_challenges : Finset (ZMod q) := Finset.univ
  have h_field_card_nat : Fintype.card (ZMod q) ≥ 2 := by
    simpa [Fintype.card_zmod] using (Fact.out (Nat.Prime q)).two_le
  have h_field_card_real : (Fintype.card (ZMod q) : ℝ) ≥ 2 := by
    exact_mod_cast h_field_card_nat
  have h_valid_card_eq : (valid_challenges.card : ℝ) = (Fintype.card (ZMod q) : ℝ) := by
    simp [valid_challenges]
  have h_heavy' : ε * (Fintype.card (ZMod q) : ℝ) ≤ (Fintype.card (ZMod q) : ℝ) := by
    have h_nonneg : 0 ≤ (Fintype.card (ZMod q) : ℝ) := by
      exact_mod_cast (Nat.zero_le (Fintype.card (ZMod q)))
    have := mul_le_mul_of_nonneg_right hε_le h_nonneg
    simpa [one_mul] using this
  have h_heavy : (valid_challenges.card : ℝ) ≥
      ε * (Fintype.card (ZMod q) : ℝ) := by
    simpa [h_valid_card_eq] using h_heavy'
  have h_nonempty : valid_challenges.card ≥ 2 := by
    simpa [valid_challenges] using h_field_card_nat
  have h_bound :=
    fork_success_bound (VC := VC)
      (state := state)
      (valid_challenges := valid_challenges)
      (ε := ε)
      h_heavy
      hε_pos
      hε_le
      h_field_card_real
      h_nonempty
  have h_pairs :
      (Nat.choose valid_challenges.card 2 : ℝ) /
          (Nat.choose (Fintype.card (ZMod q)) 2 : ℝ) = 1 := by
    have h_choose_pos :
        (Nat.choose (Fintype.card (ZMod q)) 2 : ℝ) > 0 := by
      have h_two_le : 2 ≤ Fintype.card (ZMod q) := h_field_card_nat
      simpa using
        (choose_two_pos (n := Fintype.card (ZMod q)) h_two_le)
    have h_choose_ne_zero :
        (Nat.choose (Fintype.card (ZMod q)) 2 : ℝ) ≠ 0 := ne_of_gt h_choose_pos
    simp [valid_challenges, h_choose_ne_zero]
  have h_card_cast : (Fintype.card (ZMod q) : ℝ) = (q : ℝ) := by
    simp [Fintype.card_zmod]
  simpa [h_pairs, h_card_cast]

section ZMod2

open scoped BigOperators

/-- Edge-case check: for `|F| = 2` and `ε = 1`, the fork success bound reduces to the
non-negative inequality `1 ≥ 0`. -/
lemma fork_success_bound_zmod2_eps_one :
    1 ≥ (1 : ℝ) ^ 2 / 2 - 1 / (2 : ℝ) := by
  have h := fork_success_bound_zmod_univ (q := 2) (ε := (1 : ℝ))
      (by norm_num) (by norm_num)
  simpa [Fintype.card_zmod] using h

/-- Edge-case check: with `ε = 1/2` and `|F| = 2` we still retain a positive lower
bound from `fork_success_bound`. -/
lemma fork_success_bound_zmod2_eps_half :
    1 ≥ (1 / (2 : ℝ)) ^ 2 / 2 - 1 / (2 : ℝ) := by
  have h := fork_success_bound_zmod_univ (q := 2) (ε := 1 / (2 : ℝ))
      (by norm_num) (by norm_num)
  simpa [Fintype.card_zmod, one_div, pow_two] using h

end ZMod2

section ZMod3

open scoped BigOperators

/-- Regression guard: field size 3 with maximal success margin still respects the
restored fork lower bound. -/
lemma fork_success_bound_zmod3_eps_one :
    1 ≥ (1 : ℝ) ^ 2 / 2 - 1 / (3 : ℝ) := by
  have h := fork_success_bound_zmod_univ (q := 3) (ε := (1 : ℝ))
      (by norm_num) (by norm_num)
  simpa [Fintype.card_zmod, pow_two] using h

/-- Regression guard: ε = 2/3 for |F| = 3 yields the expected negative offset. -/
lemma fork_success_bound_zmod3_eps_two_thirds :
    1 ≥ (2 / (3 : ℝ)) ^ 2 / 2 - 1 / (3 : ℝ) := by
  have h := fork_success_bound_zmod_univ (q := 3) (ε := 2 / (3 : ℝ))
      (by norm_num) (by norm_num)
  simpa [Fintype.card_zmod, pow_two, one_div] using h

/-- Regression guard: ε = 1/3 for |F| = 3 remains within the universal bound. -/
lemma fork_success_bound_zmod3_eps_third :
    1 ≥ (1 / (3 : ℝ)) ^ 2 / 2 - 1 / (3 : ℝ) := by
  have h := fork_success_bound_zmod_univ (q := 3) (ε := 1 / (3 : ℝ))
      (by norm_num) (by norm_num)
  simpa [Fintype.card_zmod, pow_two, one_div] using h

end ZMod3

section ZMod5

open scoped BigOperators

/-- Regression guard: maximal success margin for |F| = 5 matches the surcharge term. -/
lemma fork_success_bound_zmod5_eps_one :
    1 ≥ (1 : ℝ) ^ 2 / 2 - 1 / (5 : ℝ) := by
  have h := fork_success_bound_zmod_univ (q := 5) (ε := (1 : ℝ))
      (by norm_num) (by norm_num)
  simpa [Fintype.card_zmod, pow_two] using h

/-- Regression guard: ε = 4/5 for |F| = 5 stays above the negl(λ) allowance. -/
lemma fork_success_bound_zmod5_eps_four_fifths :
    1 ≥ (4 / (5 : ℝ)) ^ 2 / 2 - 1 / (5 : ℝ) := by
  have h := fork_success_bound_zmod_univ (q := 5) (ε := 4 / (5 : ℝ))
      (by norm_num) (by norm_num)
  simpa [Fintype.card_zmod, pow_two, one_div] using h

/-- Regression guard: ε = 2/5 for |F| = 5 illustrates behaviour for smaller heavy sets. -/
lemma fork_success_bound_zmod5_eps_two_fifths :
    1 ≥ (2 / (5 : ℝ)) ^ 2 / 2 - 1 / (5 : ℝ) := by
  have h := fork_success_bound_zmod_univ (q := 5) (ε := 2 / (5 : ℝ))
      (by norm_num) (by norm_num)
  simpa [Fintype.card_zmod, pow_two, one_div] using h

end ZMod5

end

end LambdaSNARK.Tests
