import BianchiIX.Dynamics.StableClockStrongVariation
import BianchiIX.Dynamics.StableClockCenterVariation
import BianchiIX.Dynamics.StableInputWeights

noncomputable section

namespace BianchiIX

theorem stableClockFlow_stable_variation_weighted {c σ : ℝ} {y : StableState}
    (hc : 2 ≤ c) (hy : y ∈ stableParameterDomain c) (hσ : 0 ≤ σ) (v : StableState) :
    ‖![fderiv ℝ (stableClockFlow c) (y, σ) (v, 0) 1,
        fderiv ℝ (stableClockFlow c) (y, σ) (v, 0) 2]‖ ≤
      8 * Real.exp (32 * (|y 1| + |y 2|)) * stableFirstInputWeight (|y 1| + |y 2|) v *
        Real.exp (-σ / 8) := by
  have hE : 1 ≤ Real.exp (32 * (|y 1| + |y 2|)) := Real.one_le_exp (by positivity)
  have H := mul_le_mul_of_nonneg_right hE (norm_nonneg (![v 1, v 2] : Fin 2 → ℝ))
  apply (stableClockFlow_stable_variation_decay hc hy hσ v).trans
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  unfold stableFirstInputWeight
  nlinarith only [H, norm_nonneg (![v 1, v 2] : Fin 2 → ℝ)]

theorem stableClockFlow_strong_variation_budget {c σ : ℝ} {y : StableState}
    (hc : 2 ≤ c) (hy : y ∈ stableParameterDomain c) (hσ : 0 ≤ σ) (v : StableState) :
    |fderiv ℝ (stableClockFlow c) (y, σ) (v, 0) 1| ≤
      (|v 1| + 16 * |y 1| * Real.exp (32 * (|y 1| + |y 2|)) * ‖v‖) *
        Real.exp (-(c + 1) / 16 * σ) := by
  have hK : 0 < c + 1 := by linarith
  apply (stableClockFlow_strong_variation_decay hc hy hσ v).trans
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  apply add_le_add (le_refl _)
  apply (div_le_iff₀ hK).mpr
  have H := mul_le_mul_of_nonneg_right (show (32 : ℝ) ≤ 16 * (c + 1) by linarith)
    (show 0 ≤ |y 1| * Real.exp (32 * (|y 1| + |y 2|)) * ‖v‖ by positivity)
  nlinarith only [H]

end BianchiIX
