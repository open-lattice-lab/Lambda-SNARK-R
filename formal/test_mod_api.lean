import Mathlib

#check @Polynomial.mod_eq_zero_iff_dvd
#check @EuclideanDomain.mod_eq_zero_iff_dvd
#check @mod_eq_zero_iff_dvd
#check Polynomial.degree_mod_lt
#check dvd_iff_mod_eq_zero

example {F : Type*} [Field F] (g f : Polynomial F) (h : IsUnit g) : f % g = 0 := by
  have hd : g ∣ f := by
    obtain ⟨c, hc⟩ := h
    use f * ↑c⁻¹
    calc g * (f * ↑c⁻¹)
      = ↑c * (f * ↑c⁻¹) := by rw [← hc]
      _ = f * (↑c * ↑c⁻¹) := by ring
      _ = f := by simp
  exact mod_eq_zero_iff_dvd.mpr hd
