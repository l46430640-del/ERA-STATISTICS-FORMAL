import BianchiIX.Dynamics.StableHessianBounds
import BianchiIX.Dynamics.StableBoundaryStrongVariation

noncomputable section

namespace BianchiIX

theorem stableDenomGradient_split_bound {y : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 10) (v : StableState) :
    |dotProduct (stableDenomGradient y) v| ≤
      2 * (c + 1) * |v 0| + 4 * (|y 1| + |y 2|) * ‖v‖ := by
  obtain ⟨_, _, hm0, hmK, _, _⟩ := stable_boundary_band hc hm
  have hdiff : |v 1 - v 2| ≤ 2 * ‖v‖ := by
    have h1 := norm_le_pi_norm v 1
    have h2 := norm_le_pi_norm v 2
    simp only [Real.norm_eq_abs] at h1 h2
    exact (abs_sub _ _).trans (by linarith)
  have H0 := mul_le_mul_of_nonneg_right (show |y 0| ≤ c + 1 by rwa [abs_of_nonneg hm0]) (abs_nonneg (v 0))
  have H1 := mul_le_mul (abs_sub (y 1) (y 2)) hdiff (abs_nonneg _) (by positivity)
  rw [stableDenomGradient_dotProduct]
  have H := abs_add_le (2 * y 0 * v 0) (2 * (y 1 - y 2) * (v 1 - v 2))
  simp only [abs_mul] at H
  norm_num only at H
  nlinarith only [H, H0, H1]

theorem stableBoundaryHessian_strong_bound {y : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 10) (v w : StableState) :
    |stableBoundaryHessian y v w 1| ≤
      5 * |y 1| * ‖v‖ * ‖w‖ + (c + 1) * (|v 0| * |w 1| + |v 1| * |w 0|) +
        (|y 1| + |y 2|) * (|v 1| * ‖w‖ + ‖v‖ * |w 1|) := by
  obtain ⟨_, _, hm0, hmK, _, _⟩ := stable_boundary_band hc hm
  have hv (i : Fin 3) : |v i| ≤ ‖v‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm v i
  have hw (i : Fin 3) : |w i| ≤ ‖w‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm w i
  have hp (i : Fin 3) := mul_le_mul (hv i) (hw i) (abs_nonneg _) (norm_nonneg _)
  have hT : |v 0 * w 1 + v 1 * w 0| ≤ |v 0| * |w 1| + |v 1| * |w 0| := by
    simpa only [abs_mul] using abs_add_le (v 0 * w 1) (v 1 * w 0)
  have hS : |v 1 * w 2 + v 2 * w 1| ≤ |v 1| * ‖w‖ + ‖v‖ * |w 1| := by
    have H := abs_add_le (v 1 * w 2) (v 2 * w 1)
    simp only [abs_mul] at H
    nlinarith only [H, mul_le_mul_of_nonneg_left (hw 2) (abs_nonneg (v 1)),
      mul_le_mul_of_nonneg_right (hv 2) (abs_nonneg (w 1))]
  have hM := mul_le_mul (show |y 0| ≤ c + 1 by rwa [abs_of_nonneg hm0]) hT (abs_nonneg _) (by linarith)
  have hW := mul_le_mul (show |y 2| ≤ |y 1| + |y 2| by linarith [abs_nonneg (y 1)])
    hS (abs_nonneg _) (by positivity)
  have H0 := mul_le_mul_of_nonneg_left (hp 0) (abs_nonneg (y 1))
  have H1 := mul_le_mul_of_nonneg_left (hp 1) (abs_nonneg (y 1))
  have H2 := mul_le_mul_of_nonneg_left (hp 2) (abs_nonneg (y 1))
  have Ha := abs_sub (-y 1 * v 0 * w 0) (y 0 * (v 0 * w 1 + v 1 * w 0))
  have Hb := abs_add_le (-y 1 * v 0 * w 0 - y 0 * (v 0 * w 1 + v 1 * w 0)) (3 * y 1 * v 1 * w 1)
  have Hc := abs_sub (-y 1 * v 0 * w 0 - y 0 * (v 0 * w 1 + v 1 * w 0) + 3 * y 1 * v 1 * w 1)
    (y 2 * (v 1 * w 2 + v 2 * w 1))
  have Hd := abs_sub (-y 1 * v 0 * w 0 - y 0 * (v 0 * w 1 + v 1 * w 0) + 3 * y 1 * v 1 * w 1 -
    y 2 * (v 1 * w 2 + v 2 * w 1)) (y 1 * v 2 * w 2)
  change |stableBoundaryHessian y v w 1| ≤ _ at Hd
  simp only [abs_mul, abs_neg] at Ha Hb Hc Hd
  norm_num only at Ha Hb Hc Hd
  nlinarith only [Ha, Hb, Hc, Hd, H0, H1, H2, hM, hW]

theorem stableOriginalField_strong_bound {y : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 10)
    (hu : |y 1| ≤ 1 / 100) (hw : |y 2| ≤ 1 / 100) :
    |stableOriginalField y 1| ≤ 6 * |y 1| := by
  have H := mul_le_mul_of_nonneg_left (stableBoundary_field_div_bounds hc hm hu hw).1
    (by norm_num : (0 : ℝ) ≤ 6)
  change |(6 / stableBoundaryDenom y) * stableBoundaryField y 1| ≤ _
  rw [show (6 / stableBoundaryDenom y) * stableBoundaryField y 1 =
    6 * (stableBoundaryField y 1 / stableBoundaryDenom y) by ring, abs_mul]
  norm_num only
  exact H

theorem stableRescaledJacobian_strong_offDiagonal {y v : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 10)
    (hu : |y 1| ≤ 1 / 100) (hw : |y 2| ≤ 1 / 100) :
    |(c + 1) * stableOriginalJacobian y 1 0 * v 0 +
      (c + 1) * stableOriginalJacobian y 1 2 * v 2| ≤ 96 * |y 1| * ‖v‖ := by
  have h0 := (stableRescaledJacobian_center_column hc hm hu hw).1
  have h2 : |(c + 1) * stableOriginalJacobian y 1 2| ≤ 18 * |y 1| :=
    (stableRescaledJacobian_strong_weak hc hm hu hw).trans
      (mul_le_of_le_one_right (by positivity) (by linarith : |y 1| + |y 2| ≤ 1))
  have hv (i : Fin 3) : |v i| ≤ ‖v‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm v i
  have H0 := mul_le_mul h0 (hv 0) (abs_nonneg _) (by positivity)
  have H2 := mul_le_mul h2 (hv 2) (abs_nonneg _) (by positivity)
  have H := abs_add_le ((c + 1) * stableOriginalJacobian y 1 0 * v 0)
    ((c + 1) * stableOriginalJacobian y 1 2 * v 2)
  simp only [abs_mul] at H H0 H2
  nlinarith only [H, H0, H2, mul_nonneg (abs_nonneg (y 1)) (norm_nonneg v)]

theorem stableRescaledJacobian_strong_apply {y : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 10)
    (hu : |y 1| ≤ 1 / 100) (hw : |y 2| ≤ 1 / 100) (v : StableState) :
    |(c + 1) * (stableOriginalJacobian y).mulVec v 1| ≤
      96 * |y 1| * ‖v‖ + 18 * (c + 1) * |v 1| := by
  have hK : 0 < c + 1 := by linarith
  have hd : |(c + 1) * stableOriginalJacobian y 1 1 * v 1| ≤ 18 * (c + 1) * |v 1| := by
    rw [abs_mul, abs_mul, abs_of_pos hK]
    have H := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (stableOriginalJacobian_wall_bound hc hm hu hw 1 1 (by decide)) hK.le)
      (abs_nonneg (v 1))
    nlinarith only [H]
  have heq : (c + 1) * (stableOriginalJacobian y).mulVec v 1 =
      ((c + 1) * stableOriginalJacobian y 1 0 * v 0 + (c + 1) * stableOriginalJacobian y 1 2 * v 2) +
        (c + 1) * stableOriginalJacobian y 1 1 * v 1 := by
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    ring
  rw [heq]
  exact (abs_add_le _ _).trans (add_le_add (stableRescaledJacobian_strong_offDiagonal hc hm hu hw) hd)

end BianchiIX
