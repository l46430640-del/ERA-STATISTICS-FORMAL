import BianchiIX.Analysis.ReciprocalDifference
import Mathlib.Analysis.Calculus.Deriv.Add

noncomputable section

namespace BianchiIX

theorem hasDerivAt_reciprocal_error {f k : ℝ → ℝ} {x df dk : ℝ}
    (hf : HasDerivAt f df x) (hk : HasDerivAt k dk x) (hf0 : f x ≠ 0) (hk0 : k x ≠ 0) :
    HasDerivAt (fun y => 2 / f y - 2 / k y)
      (-2 * (df - dk) / (f x) ^ 2 +
        2 * (f x - k x) * (f x + k x) * dk / ((k x) ^ 2 * (f x) ^ 2)) x := by
  have Hf : HasDerivAt (fun y => 2 / f y) (-2 * df / (f x) ^ 2) x := by
    convert! (hasDerivAt_const x (2 : ℝ)).div hf hf0 using 1
    ring
  have Hk : HasDerivAt (fun y => 2 / k y) (-2 * dk / (k x) ^ 2) x := by
    convert! (hasDerivAt_const x (2 : ℝ)).div hk hk0 using 1
    ring
  have H : HasDerivAt (fun y => 2 / f y - 2 / k y)
      (-2 * df / (f x) ^ 2 - (-2 * dk / (k x) ^ 2)) x := Hf.sub Hk
  convert! H using 1
  field_simp
  ring

/-- Reciprocal phase loses no amplitude power when the radial difference is differentiated first. -/
theorem partial_core_reciprocal_radial_bounds {f k : ℝ → ℝ} {x r K C U P : ℝ}
    (hr : 0 < r ∧ r ≤ 1) (hK : 1 ≤ K) (hU : 0 ≤ U)
    (hP : 0 ≤ P ∧ P ≤ 1) (hf : DifferentiableAt ℝ f x) (hk : DifferentiableAt ℝ k x)
    (hklo : 2 / (K * r) ≤ k x) (hFlo : k x / 2 ≤ f x)
    (hvalue : |f x - k x| ≤ 16 * (U + P ^ 2 / k x))
    (hdk : |deriv k x| ≤ K / r ^ 2)
    (hde : |deriv f x - deriv k x| ≤ 4 * C * K ^ 2 * (U + r * P) / r ^ 2) :
    DifferentiableAt ℝ (fun y => 2 / f y - 2 / k y) x ∧
      |f x - k x| ≤ 16 * K * (U + r * P ^ 2) ∧
      |2 / f x - 2 / k x| ≤ 32 * K ^ 3 * r ^ 2 * (U + r * P ^ 2) ∧
      |deriv (fun y => 2 / f y - 2 / k y) x| ≤
        (8 * C * K ^ 4 + 64 * K ^ 5) * (U + r * P) := by
  have hr0 := hr.1
  have hK0 : 0 < K := by linarith only [hK]
  have hKr : 0 < K * r := mul_pos hK0 hr.1
  have hk0 : 0 < k x := (div_pos (by norm_num) hKr).trans_le hklo
  have hF0 : 0 < f x := (half_pos hk0).trans_le hFlo
  have hkhalf : 1 / (K * r) ≤ k x / 2 := by
    have heq : 2 / (K * r) = 2 * (1 / (K * r)) := by ring
    rw [heq] at hklo
    linarith only [hklo]
  have hkα : 1 / (K * r) ≤ k x := hkhalf.trans (by linarith only [hk0])
  have hfα : 1 / (K * r) ≤ f x := hkhalf.trans hFlo
  have hki : 1 / k x ≤ K * r := by
    apply (div_le_iff₀ hk0).mpr
    nlinarith only [(div_le_iff₀ hKr).mp hkα]
  have he : |f x - k x| ≤ 16 * K * (U + r * P ^ 2) := hvalue.trans (by
    have H₁ := mul_le_mul_of_nonneg_left hK hU
    have H₂ := mul_le_mul_of_nonneg_left hki (sq_nonneg P)
    simp only [mul_one_div] at H₂
    nlinarith only [H₁, H₂])
  have HD := hasDerivAt_reciprocal_error hf.hasDerivAt hk.hasDerivAt hF0.ne' hk0.ne'
  refine ⟨HD.differentiableAt, he, ?_, ?_⟩
  · exact (reciprocal_difference_value_bound hKr hfα hkα).trans
      ((mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ 2 * (K * r) ^ 2)).trans_eq (by ring))
  · have hq : |deriv k x| ≤ K ^ 3 / (K * r) ^ 2 := hdk.trans_eq (by field_simp)
    have H := reciprocal_difference_derivative_bound hKr hfα hkα hq
      (Θ := f x - k x) (p := deriv f x - deriv k x)
    have H₁ : 2 * (K * r) ^ 2 * |deriv f x - deriv k x| ≤
        8 * C * K ^ 4 * (U + r * P) :=
      (mul_le_mul_of_nonneg_left hde (by positivity)).trans_eq (by field_simp; ring)
    have hPr : 0 ≤ P * r ∧ P * r ≤ 1 :=
      ⟨mul_nonneg hP.1 hr.1.le, (mul_le_mul_of_nonneg_right hP.2 hr.1.le).trans (by simpa using hr.2)⟩
    have hsmall : r * (U + r * P ^ 2) ≤ U + r * P := by
      nlinarith only [mul_le_mul_of_nonneg_left hr.2 hU,
        mul_le_mul_of_nonneg_right hPr.2 hPr.1]
    have H₂ : 4 * K ^ 3 * (K * r) * |f x - k x| ≤ 64 * K ^ 5 * (U + r * P) := by
      calc
        _ ≤ 4 * K ^ 3 * (K * r) * (16 * K * (U + r * P ^ 2)) :=
          mul_le_mul_of_nonneg_left he (by positivity)
        _ = (64 * K ^ 5) * (r * (U + r * P ^ 2)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hsmall (by positivity)
    rw [HD.deriv]
    exact H.trans ((add_le_add H₁ H₂).trans_eq (by ring))

end BianchiIX
