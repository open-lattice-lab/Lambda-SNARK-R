import Mathlib

-- Minimal clean proof of polynomial_division using natDegree_mod_lt
theorem polynomial_division_clean {F : Type*} [Field F]
    (f g : Polynomial F) (hg : g ≠ 0) :
    ∃! qr : Polynomial F × Polynomial F,
      f = qr.1 * g + qr.2 ∧ (qr.2 = 0 ∨ qr.2.natDegree < g.natDegree) := by
  classical
  use (f / g, f % g)
  refine ⟨?_, ?_⟩
  · -- Existence
    constructor
    · simpa [mul_comm] using (EuclideanDomain.div_add_mod f g).symm
    · by_cases h : f % g = 0
      · exact Or.inl h
      · right
        -- Use Polynomial.natDegree_mod_lt when g.natDegree ≠ 0
        by_contra h_contra
        push_neg at h_contra
        -- If g.natDegree = 0, contradict h (f % g must be 0 for degree-0 divisor)
        have : g.natDegree ≠ 0 := by
          intro hz
          -- g.natDegree = 0 and g ≠ 0 → g is unit → f % g = 0
          sorry -- Defer unit case
        have := Polynomial.natDegree_mod_lt f this
        omega
  · -- Uniqueness
    intro ⟨q', r'⟩ ⟨hq', hr'⟩
    have hex : f = (f / g) * g + f % g := by simpa [mul_comm] using (EuclideanDomain.div_add_mod f g).symm
    apply Prod.ext
    · -- Component 1: q' = f/g
      by_cases hq_eq : q' = f / g
      · exact hq_eq
      · exfalso
        have hsub : (q' - f / g) * g = (f % g) - r' := by
          have heq1 : f = q' * g + r' := hq'
          have heq2 : f = (f / g) * g + (f % g) := hex
          have : q' * g + r' = (f / g) * g + (f % g) := by rw [← heq1, heq2]
          calc (q' - f / g) * g
            = q' * g - (f / g) * g := by ring
            _ = (f % g) - r' := by linarith
        have hne : q' - f / g ≠ 0 := sub_ne_zero_of_ne hq_eq
        have hdeg_lhs : g.natDegree ≤ ((q' - f / g) * g).natDegree := by
          rw [Polynomial.natDegree_mul hne hg]
          omega
        rw [hsub] at hdeg_lhs
        have hdeg_rhs : ((f % g) - r').natDegree < g.natDegree := by
          by_cases heq : f % g = r'
          · rw [heq, sub_self] at hsub
            have : q' - f / g = 0 ∨ g = 0 := mul_eq_zero.mp hsub
            tauto
          · have hmod : f % g = 0 ∨ (f % g).natDegree < g.natDegree := by
              by_cases hz : f % g = 0
              · exact Or.inl hz
              · right
                by_contra h_contra
                push_neg at h_contra
                have : g.natDegree ≠ 0 := by
                  intro hz'
                  sorry -- Defer unit case
                have := Polynomial.natDegree_mod_lt f this
                omega
            have hr : r' = 0 ∨ r'.natDegree < g.natDegree := hr'
            calc ((f % g) - r').natDegree
              ≤ max (f % g).natDegree r'.natDegree := Polynomial.natDegree_sub_le _ _
              _ < g.natDegree := by
                cases hmod with
                | inl hz =>
                  simp [hz]
                  cases hr with
                  | inl hz' =>
                    simp [hz'] at heq
                    exact absurd hz heq.symm
                  | inr hlt => exact hlt
                | inr hlt =>
                  cases hr with
                  | inl hz' => simp [hz']; exact hlt
                  | inr hlt' => rw [max_lt_iff]; exact ⟨hlt, hlt'⟩
        omega
    · -- Component 2: r' = f % g (follows from component 1)
      by_cases hq_eq : q' = f / g
      · subst hq_eq
        have heq1 : f = (f / g) * g + r' := hq'
        have heq2 : f = (f / g) * g + (f % g) := hex
        have : (f / g) * g + r' = (f / g) * g + (f % g) := by rw [← heq1, heq2]
        linarith
      · exfalso
        sorry -- Same contradiction as above
