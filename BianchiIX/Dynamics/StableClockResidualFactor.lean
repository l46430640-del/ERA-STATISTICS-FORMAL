import BianchiIX.Dynamics.StableClockTail
import BianchiIX.Dynamics.StableScaledResidualDerivatives
import BianchiIX.Dynamics.StableHessianClockBounds

noncomputable section

namespace BianchiIX

def stableClockResidualFactor (c : ℝ) (y : StableState) : ℝ :=
  (6 * (c + 1) ^ 2)⁻¹ * stableBoundaryDenom y

def stableClockResidualState (c : ℝ) (y : StableState) : ℝ :=
  stableCorrectedResidual (y 0) (y 1) (y 2) / (c + 1)

theorem contDiff_stableClockResidualFactor (c : ℝ) (n : WithTop ℕ∞) :
    ContDiff ℝ n (stableClockResidualFactor c) :=
  contDiff_const.mul (contDiff_stableBoundaryDenom n)

theorem stableClockResidualFactor_fderiv (c : ℝ) (y v : StableState) :
    fderiv ℝ (stableClockResidualFactor c) y v =
      (6 * (c + 1) ^ 2)⁻¹ * dotProduct (stableDenomGradient y) v := by
  unfold stableClockResidualFactor
  rw [fderiv_const_mul ((contDiff_stableBoundaryDenom 1).differentiable (by norm_num) y)]
  simp only [smul_apply, smul_eq_mul, stableBoundaryDenom_fderiv]

theorem stableClockResidualFactor_fderiv2 (c : ℝ) (y v w : StableState) :
    fderiv ℝ (fderiv ℝ (stableClockResidualFactor c)) y v w =
      (6 * (c + 1) ^ 2)⁻¹ * stableDenomHessian v w := by
  unfold stableClockResidualFactor
  rw [fderiv2_mul_apply contDiffAt_const (contDiff_stableBoundaryDenom 2).contDiffAt]
  have hz : fderiv ℝ (fun _ : StableState => (6 * (c + 1) ^ 2)⁻¹) = fun _ => 0 :=
    funext (fun _ => fderiv_const_apply _)
  simp only [hz, fderiv_const_apply, zero_apply, zero_mul, add_zero, stableBoundaryDenom_fderiv2]

theorem stableClockResidualState_factor {c : ℝ} (hc : 2 ≤ c) (y : StableState) :
    stableClockResidualState c y = stableClockResidualFactor c y * stableScaledResidual (c + 1) y := by
  have hK : c + 1 ≠ 0 := by linarith
  have hD := (stableBoundaryDenom_pos y).ne'
  unfold stableClockResidualState stableClockResidualFactor stableScaledResidual stableResidualClock
  field_simp

theorem stableClockResidualFactor_bounds {c : ℝ} {y : StableState}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 10)
    (hu : |y 1| ≤ 1 / 100) (hw : |y 2| ≤ 1 / 100) :
    |stableClockResidualFactor c y| ≤ 1 ∧
      (∀ v, |fderiv ℝ (stableClockResidualFactor c) y v| ≤ ‖v‖) ∧
      (∀ v w, |fderiv ℝ (fderiv ℝ (stableClockResidualFactor c)) y v w| ≤ ‖v‖ * ‖w‖) := by
  obtain ⟨hK, _, hm0, hmK, _, _⟩ := stable_boundary_band hc hm
  have hden : 0 < 6 * (c + 1) ^ 2 := by positivity
  have hden6 : 6 * (c + 1) ≤ 6 * (c + 1) ^ 2 := by nlinarith
  have hden10 : 10 ≤ 6 * (c + 1) ^ 2 := by nlinarith
  refine ⟨?_, ?_, ?_⟩
  · have hdiff : |y 1 - y 2| ≤ 1 / 50 := (abs_sub _ _).trans (by linarith)
    have hdiff2 := (sq_le_sq).mpr (show |y 1 - y 2| ≤ |(1 / 50 : ℝ)| by norm_num; exact hdiff)
    have hm2 := (sq_le_sq₀ hm0 (by linarith : 0 ≤ c + 1)).mpr hmK
    unfold stableClockResidualFactor
    rw [abs_mul, abs_of_pos (inv_pos.mpr hden), abs_of_pos (stableBoundaryDenom_pos y)]
    rw [inv_mul_eq_div]
    apply (div_le_iff₀ hden).mpr
    unfold stableBoundaryDenom
    nlinarith
  · intro v
    rw [stableClockResidualFactor_fderiv, abs_mul, abs_of_pos (inv_pos.mpr hden), inv_mul_eq_div]
    apply (div_le_iff₀ hden).mpr
    have H := mul_le_mul_of_nonneg_right hden6 (norm_nonneg v)
    nlinarith only [H, stableDenomGradient_bound hc hm hu hw v]
  · intro v w
    rw [stableClockResidualFactor_fderiv2, abs_mul, abs_of_pos (inv_pos.mpr hden), inv_mul_eq_div]
    apply (div_le_iff₀ hden).mpr
    have H := mul_le_mul_of_nonneg_right hden10 (show 0 ≤ ‖v‖ * ‖w‖ by positivity)
    nlinarith only [H, stableDenomHessian_bound v w]

end BianchiIX
