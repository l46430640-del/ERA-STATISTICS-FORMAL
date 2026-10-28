import BianchiIX.Dynamics.StableResidualClock

noncomputable section

namespace BianchiIX

theorem stableResidualClock_bound {y : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 10) :
    |stableResidualClock (c + 1) y| ≤ 18 / (c + 1) := by
  have hK : 0 < c + 1 := by linarith
  have hD := stableBoundaryDenom_pos y
  rw [stableResidualClock, abs_of_pos (by positivity)]
  apply (div_le_div_iff₀ hD hK).mpr
  nlinarith [(stableBoundaryDenom_lower hc hm).1]

theorem stableDenomGradient_ratio_bound {y : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 10)
    (hu : |y 1| ≤ 1 / 100) (hw : |y 2| ≤ 1 / 100) (v : StableState) :
    |dotProduct (stableDenomGradient y) v / stableBoundaryDenom y| ≤ 6 * ‖v‖ := by
  rw [abs_div, abs_of_pos (stableBoundaryDenom_pos y)]
  apply (div_le_iff₀ (stableBoundaryDenom_pos y)).mpr
  have H := mul_le_mul_of_nonneg_right (stableBoundaryDenom_lower hc hm).2 (show 0 ≤ 6 * ‖v‖ by positivity)
  nlinarith only [H, stableDenomGradient_bound hc hm hu hw v]

theorem stableResidualClock_first_bound {y : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 10)
    (hu : |y 1| ≤ 1 / 100) (hw : |y 2| ≤ 1 / 100) (v : StableState) :
    |fderiv ℝ (stableResidualClock (c + 1)) y v| ≤ 108 / (c + 1) * ‖v‖ := by
  have hK : 0 < c + 1 := by linarith
  rw [stableResidualClock_fderiv]
  have heq : -(6 * (c + 1) / stableBoundaryDenom y ^ 2) * dotProduct (stableDenomGradient y) v =
      -stableResidualClock (c + 1) y * (dotProduct (stableDenomGradient y) v / stableBoundaryDenom y) := by
    unfold stableResidualClock
    ring
  rw [heq, abs_mul, abs_neg]
  have H := mul_le_mul (stableResidualClock_bound hc hm) (stableDenomGradient_ratio_bound hc hm hu hw v)
    (abs_nonneg _) (by positivity : 0 ≤ 18 / (c + 1))
  convert! H using 1
  ring

theorem stableResidualClock_second_bound {y : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 10)
    (hu : |y 1| ≤ 1 / 100) (hw : |y 2| ≤ 1 / 100) (v w : StableState) :
    |fderiv ℝ (fderiv ℝ (stableResidualClock (c + 1))) y v w| ≤ 1476 / (c + 1) * ‖v‖ * ‖w‖ := by
  have hK : 0 < c + 1 := by linarith
  have hD := stableBoundaryDenom_pos y
  have hD1 : 1 ≤ stableBoundaryDenom y := by
    have H := (stableBoundaryDenom_lower hc hm).2
    linarith
  have H1 := mul_le_mul (stableDenomGradient_ratio_bound hc hm hu hw v)
    (stableDenomGradient_ratio_bound hc hm hu hw w) (abs_nonneg _) (by positivity : 0 ≤ 6 * ‖v‖)
  have H2 : |stableDenomHessian v w / stableBoundaryDenom y| ≤ 10 * ‖v‖ * ‖w‖ := by
    rw [abs_div, abs_of_pos hD]
    apply (div_le_iff₀ hD).mpr
    have H := mul_le_mul_of_nonneg_left hD1 (show 0 ≤ 10 * ‖v‖ * ‖w‖ by positivity)
    nlinarith only [H, stableDenomHessian_bound v w]
  have H3 : |2 * (dotProduct (stableDenomGradient y) v / stableBoundaryDenom y) *
      (dotProduct (stableDenomGradient y) w / stableBoundaryDenom y) -
      stableDenomHessian v w / stableBoundaryDenom y| ≤ 82 * ‖v‖ * ‖w‖ := by
    have H := abs_sub (2 * (dotProduct (stableDenomGradient y) v / stableBoundaryDenom y) *
      (dotProduct (stableDenomGradient y) w / stableBoundaryDenom y)) (stableDenomHessian v w / stableBoundaryDenom y)
    simp only [abs_mul] at H
    norm_num only at H
    nlinarith only [H, H1, H2]
  rw [stableResidualClock_fderiv2, abs_mul]
  have H := mul_le_mul (stableResidualClock_bound hc hm) H3 (abs_nonneg _) (by positivity : 0 ≤ 18 / (c + 1))
  convert! H using 1
  ring

theorem stableResidualClock_derivative_bounds {y : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 10)
    (hu : |y 1| ≤ 1 / 100) (hw : |y 2| ≤ 1 / 100) :
    |stableResidualClock (c + 1) y| ≤ 1500 / (c + 1) ∧
      ‖fderiv ℝ (stableResidualClock (c + 1)) y‖ ≤ 1500 / (c + 1) ∧
      ‖fderiv ℝ (fderiv ℝ (stableResidualClock (c + 1))) y‖ ≤ 1500 / (c + 1) := by
  have hK : 0 < c + 1 := by linarith
  refine ⟨(stableResidualClock_bound hc hm).trans (div_le_div_of_nonneg_right (by norm_num) hK.le), ?_, ?_⟩
  · apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro v
    exact (stableResidualClock_first_bound hc hm hu hw v).trans
      (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (by norm_num) hK.le) (norm_nonneg v))
  · apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro v
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro w
    exact (stableResidualClock_second_bound hc hm hu hw v w).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (by norm_num) hK.le) (norm_nonneg v)) (norm_nonneg w))

end BianchiIX
