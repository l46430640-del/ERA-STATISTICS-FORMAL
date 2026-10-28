import BianchiIX.Analysis.CoreIntegrals

noncomputable section

namespace BianchiIX

/-- A fixed upper entry angle leaves a uniform positive angle before the outgoing section. -/
theorem partial_core_angle_gap {k z₀ z₁ Z : ℝ} (hk : 0 < k) (hZ : 0 ≤ Z)
    (hz₀ : z₀ ≤ Z) (hz₁ : 0 ≤ z₁)
    (hentry : Real.cosh Z ≤ k / 2) (hexit : 99 / 100 * k ≤ Real.cosh z₁) :
    Real.log (99 / 50 : ℝ) ≤ z₁ - z₀ ∧ 49 / 99 ≤ z₁ - z₀ ∧ 1 / 3 < z₁ - z₀ := by
  have horder : Z ≤ z₁ := by
    have H : Real.cosh Z ≤ Real.cosh z₁ := by linarith only [hentry, hexit, hk]
    simpa only [abs_of_nonneg hZ, abs_of_nonneg hz₁] using Real.cosh_le_cosh.mp H
  have H := sech_le_exp (neg_le_neg horder)
  rw [Real.cosh_neg, Real.cosh_neg, show -Z - -z₁ = z₁ - Z by ring] at H
  have H' : 1 / Real.cosh Z ≤ Real.exp (z₁ - Z) / Real.cosh z₁ := by
    simpa only [one_div_mul_eq_div] using H
  have Hmul := (div_le_div_iff₀ (Real.cosh_pos Z) (Real.cosh_pos z₁)).mp H'
  have Hratio : (99 / 50 : ℝ) ≤ Real.exp (z₁ - Z) := by
    apply (mul_le_mul_iff_right₀ (Real.cosh_pos Z)).mp
    nlinarith only [hentry, hexit, Hmul]
  have Hlog : Real.log (99 / 50 : ℝ) ≤ z₁ - Z :=
    (Real.log_le_iff_le_exp (by norm_num)).mpr Hratio
  have Hnum : (49 / 99 : ℝ) ≤ Real.log (99 / 50 : ℝ) := by
    have H := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 99 / 50)
    norm_num at H
    linarith only [H]
  refine ⟨by linarith only [Hlog, hz₀], by linarith only [Hnum, Hlog, hz₀], ?_⟩
  linarith only [Hnum, Hlog, hz₀]

end BianchiIX
