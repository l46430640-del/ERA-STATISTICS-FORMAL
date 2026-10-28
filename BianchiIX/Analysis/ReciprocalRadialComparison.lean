import BianchiIX.Analysis.PartialCoreReciprocalError

noncomputable section

namespace BianchiIX

/-- Bounded radius displacement and an inverse-scale derivative error give quadratic
reciprocal-phase displacement and a linear ordinary derivative error. -/
theorem reciprocal_radial_comparison {f k : ℝ → ℝ} {x r L D V E : ℝ}
    (hr : 0 < r) (hL : 0 < L) (hD : 0 ≤ D)
    (hf : DifferentiableAt ℝ f x) (hk : DifferentiableAt ℝ k x)
    (hflo : 1 / (L * r) ≤ f x) (hklo : 1 / (L * r) ≤ k x)
    (hvalue : |f x - k x| ≤ V) (hdk : |deriv k x| ≤ D / r ^ 2)
    (hde : |deriv f x - deriv k x| ≤ E / r) :
    DifferentiableAt ℝ (fun t => 2 / f t - 2 / k t) x ∧
      |2 / f x - 2 / k x| ≤ 2 * L ^ 2 * V * r ^ 2 ∧
      |deriv (fun t => 2 / f t - 2 / k t) x| ≤ (2 * L ^ 2 * E + 4 * D * L ^ 3 * V) * r := by
  have hLr : 0 < L * r := mul_pos hL hr
  have hf0 : 0 < f x := (one_div_pos.mpr hLr).trans_le hflo
  have hk0 : 0 < k x := (one_div_pos.mpr hLr).trans_le hklo
  have HD := hasDerivAt_reciprocal_error hf.hasDerivAt hk.hasDerivAt hf0.ne' hk0.ne'
  have hq : |deriv k x| ≤ (D * L ^ 2) / (L * r) ^ 2 := hdk.trans_eq (by field_simp)
  have HB := reciprocal_difference_derivative_bound hLr hflo hklo hq
    (Θ := f x - k x) (p := deriv f x - deriv k x)
  refine ⟨HD.differentiableAt, ?_, ?_⟩
  · exact (reciprocal_difference_value_bound hLr hflo hklo).trans
      ((mul_le_mul_of_nonneg_left hvalue (by positivity)).trans_eq (by ring))
  · rw [HD.deriv]
    apply HB.trans
    calc
      _ ≤ 2 * (L * r) ^ 2 * (E / r) + 4 * (D * L ^ 2) * (L * r) * V :=
        add_le_add (mul_le_mul_of_nonneg_left hde (by positivity))
          (mul_le_mul_of_nonneg_left hvalue (by positivity))
      _ = _ := by field_simp

end BianchiIX
