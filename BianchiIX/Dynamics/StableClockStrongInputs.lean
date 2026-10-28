import BianchiIX.Dynamics.StableClockStrongSecondVariation
import BianchiIX.Dynamics.StableSecondStrongInputs

noncomputable section

namespace BianchiIX

theorem stableClockFlow_variation_factor_le {c : ℝ} {y : StableState}
    (hy : y ∈ stableParameterDomain c) :
    Real.exp (32 * (|y 1| + |y 2|)) ≤ Real.exp (8 / 25) :=
  Real.exp_le_exp.mpr (by linarith [hy.2.1, hy.2.2])

theorem stableClockFlow_strong_variation_noStrongInputs {c σ : ℝ} {y v : StableState}
    (hc : 2 ≤ c) (hy : y ∈ stableParameterDomain c) (hσ : 0 ≤ σ) (hv : v 1 = 0) :
    |fderiv ℝ (stableClockFlow c) (y, σ) (v, 0) 1| ≤
      32 * |y 1| * Real.exp (32 * (|y 1| + |y 2|)) * ‖v‖ / (c + 1) *
        Real.exp (-(c + 1) / 16 * σ) := by
  simpa only [hv, abs_zero, zero_add] using stableClockFlow_strong_variation_decay hc hy hσ v

theorem stableClockFlow_strong_variation_uniform {c σ : ℝ} {y : StableState}
    (hc : 2 ≤ c) (hy : y ∈ stableParameterDomain c) (hσ : 0 ≤ σ) (v : StableState) :
    |fderiv ℝ (stableClockFlow c) (y, σ) (v, 0) 1| ≤
      2 * Real.exp (32 * (|y 1| + |y 2|)) * ‖v‖ * Real.exp (-(c + 1) / 16 * σ) := by
  have hE : 1 ≤ Real.exp (32 * (|y 1| + |y 2|)) := Real.one_le_exp (by positivity)
  have hv : |v 1| ≤ ‖v‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm v 1
  have H1 := mul_le_mul_of_nonneg_right hE (norm_nonneg v)
  have H2 := mul_le_mul_of_nonneg_right hy.2.1.le
    (show 0 ≤ Real.exp (32 * (|y 1| + |y 2|)) * ‖v‖ by positivity)
  apply (stableClockFlow_strong_variation_budget hc hy hσ v).trans
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  nlinarith only [hv, H1, H2, norm_nonneg v]

theorem stableClockFlow_strong_second_variation_noStrongInputs {c σ : ℝ} {y v w : StableState}
    (hc : 2 ≤ c) (hy : y ∈ stableParameterDomain c) (hσ : 0 ≤ σ)
    (hv : v 1 = 0) (hw : w 1 = 0) :
    |fderiv ℝ (fderiv ℝ (fun z => stableClockFlow c (z, σ))) y v w 1| ≤
      560000 * |y 1| * Real.exp (32 * (|y 1| + |y 2|)) ^ 3 * ‖v‖ * ‖w‖ /
        (c + 1) * Real.exp (-(c + 1) / 16 * σ) := by
  have H := stableClockFlow_strong_second_variation_decay hc hy hσ v w
  rw [stableStrongHessianBudget_noStrong hv hw] at H
  convert! H using 1
  ring

theorem stableClockFlow_strong_second_variation_stableInputs {c σ : ℝ} {y v w : StableState}
    (hc : 2 ≤ c) (hy : y ∈ stableParameterDomain c) (hσ : 0 ≤ σ)
    (hv : v 0 = 0) (hw : w 0 = 0) :
    |fderiv ℝ (fderiv ℝ (fun z => stableClockFlow c (z, σ))) y v w 1| ≤
      1680000 * (|y 1| + |y 2|) * Real.exp (32 * (|y 1| + |y 2|)) ^ 3 * ‖v‖ * ‖w‖ /
        (c + 1) * Real.exp (-(c + 1) / 16 * σ) := by
  have hK : 0 < c + 1 := by linarith
  have H := mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (stableStrongHessianBudget_stable (y := y) hv hw)
      (show 0 ≤ 560000 * Real.exp (32 * (|y 1| + |y 2|)) ^ 3 by positivity)) hK.le)
    (Real.exp_pos (-(c + 1) / 16 * σ)).le
  exact (stableClockFlow_strong_second_variation_decay hc hy hσ v w).trans
    (by convert! H using 1; ring)

theorem stableClockFlow_strong_second_variation_uniform {c σ : ℝ} {y : StableState}
    (hc : 2 ≤ c) (hy : y ∈ stableParameterDomain c) (hσ : 0 ≤ σ) (v w : StableState) :
    |fderiv ℝ (fderiv ℝ (fun z => stableClockFlow c (z, σ))) y v w 1| ≤
      1680000 * Real.exp (32 * (|y 1| + |y 2|)) ^ 3 * ‖v‖ * ‖w‖ /
        (c + 1) * Real.exp (-(c + 1) / 16 * σ) := by
  have hK : 0 < c + 1 := by linarith
  have hB : stableStrongHessianBudget y v w ≤ 3 * ‖v‖ * ‖w‖ :=
    (stableStrongHessianBudget_bound y v w).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (show 2 + 3 * (|y 1| + |y 2|) ≤ 3 by linarith [hy.2.1, hy.2.2]) (norm_nonneg v))
        (norm_nonneg w))
  have H := mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hB
      (show 0 ≤ 560000 * Real.exp (32 * (|y 1| + |y 2|)) ^ 3 by positivity)) hK.le)
    (Real.exp_pos (-(c + 1) / 16 * σ)).le
  exact (stableClockFlow_strong_second_variation_decay hc hy hσ v w).trans
    (by convert! H using 1; ring)

end BianchiIX
