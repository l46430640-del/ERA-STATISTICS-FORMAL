import BianchiIX.Dynamics.StableHessianPolynomialBounds

noncomputable section

namespace BianchiIX

def stableHessianBudget (y v w : StableState) : ℝ :=
  (|y 1| + |y 2|) * ‖v‖ * ‖w‖ + ‖![v 1, v 2]‖ * ‖w‖ + ‖v‖ * ‖![w 1, w 2]‖

theorem stableHessianBudget_nonneg (y v w : StableState) : 0 ≤ stableHessianBudget y v w := by
  unfold stableHessianBudget
  positivity

theorem stableRescaledJacobian_apply_bound {y : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 10)
    (hu : |y 1| ≤ 1 / 100) (hw : |y 2| ≤ 1 / 100) (v : StableState) :
    ‖(c + 1) • (stableOriginalJacobian y).mulVec v‖ ≤
      64 * (|y 1| + |y 2|) * ‖v‖ + 36 * (c + 1) * ‖![v 1, v 2]‖ := by
  have hK : 0 < c + 1 := by linarith
  have hb : 0 ≤ |y 1| + |y 2| := by positivity
  have hb1 : |y 1| + |y 2| ≤ 1 := by linarith
  have h0 (i : Fin 3) : |(c + 1) * stableOriginalJacobian y i 0| ≤ 64 * (|y 1| + |y 2|) := by
    have H := stableRescaledJacobian_center_bounds hc hm hu hw
    have H' := stableRescaledJacobian_center_column hc hm hu hw
    fin_cases i
    · exact H.1.trans (by nlinarith)
    · exact H'.1.trans (by linarith [abs_nonneg (y 2)])
    · exact H'.2.trans (by linarith [abs_nonneg (y 1)])
  have hz (i j : Fin 3) (hj : j ≠ 0) :
      |(c + 1) * stableOriginalJacobian y i j| ≤ 18 * (c + 1) := by
    rw [abs_mul, abs_of_pos hK]
    nlinarith only [mul_le_mul_of_nonneg_left (stableOriginalJacobian_wall_bound hc hm hu hw i j hj) hK.le]
  have hv0 : |v 0| ≤ ‖v‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm v 0
  have hv1 : |v 1| ≤ ‖![v 1, v 2]‖ := by simpa only [Real.norm_eq_abs, Matrix.cons_val_zero] using norm_le_pi_norm ![v 1, v 2] 0
  have hv2 : |v 2| ≤ ‖![v 1, v 2]‖ := by simpa only [Real.norm_eq_abs, Matrix.cons_val_one, Matrix.cons_val_zero] using norm_le_pi_norm ![v 1, v 2] 1
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  have heq : ((c + 1) • (stableOriginalJacobian y).mulVec v) i =
      ((c + 1) * stableOriginalJacobian y i 0) * v 0 +
        ((c + 1) * stableOriginalJacobian y i 1) * v 1 +
        ((c + 1) * stableOriginalJacobian y i 2) * v 2 := by
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    ring
  rw [heq, Real.norm_eq_abs]
  have H := (abs_add_le (((c + 1) * stableOriginalJacobian y i 0) * v 0 +
    ((c + 1) * stableOriginalJacobian y i 1) * v 1) (((c + 1) * stableOriginalJacobian y i 2) * v 2)).trans
      (add_le_add (abs_add_le _ _) (le_refl _))
  have H0 := mul_le_mul (h0 i) hv0 (abs_nonneg _) (by positivity)
  have H1 := mul_le_mul (hz i 1 (by decide)) hv1 (abs_nonneg _) (by positivity)
  have H2 := mul_le_mul (hz i 2 (by decide)) hv2 (abs_nonneg _) (by positivity)
  simp only [abs_mul] at H H0 H1 H2
  nlinarith only [H, H0, H1, H2]

theorem stableHessian_clock_term_bound {y : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 10)
    (hu : |y 1| ≤ 1 / 100) (hw : |y 2| ≤ 1 / 100) (v w : StableState) :
    ‖(dotProduct (stableDenomGradient y) v / stableBoundaryDenom y) •
        ((c + 1) • (stableOriginalJacobian y).mulVec w)‖ ≤
      384 * (|y 1| + |y 2|) * ‖v‖ * ‖w‖ + 648 * ‖v‖ * ‖![w 1, w 2]‖ := by
  have hD := stableBoundaryDenom_pos y
  have hK : 0 < c + 1 := by linarith
  have hs1 : (c + 1) / stableBoundaryDenom y ≤ 1 :=
    (div_le_one hD).mpr (stableBoundaryDenom_lower hc hm).2
  have hs2 : (c + 1) ^ 2 / stableBoundaryDenom y ≤ 3 :=
    (div_le_iff₀ hD).mpr (by nlinarith [(stableBoundaryDenom_lower hc hm).1])
  have hratio : |dotProduct (stableDenomGradient y) v / stableBoundaryDenom y| ≤
      (6 * (c + 1) / stableBoundaryDenom y) * ‖v‖ := by
    rw [abs_div, abs_of_pos hD]
    have H := div_le_div_of_nonneg_right (stableDenomGradient_bound hc hm hu hw v) hD.le
    convert! H using 1
    ring
  rw [norm_smul, Real.norm_eq_abs]
  calc
    _ ≤ ((6 * (c + 1) / stableBoundaryDenom y) * ‖v‖) *
        (64 * (|y 1| + |y 2|) * ‖w‖ + 36 * (c + 1) * ‖![w 1, w 2]‖) :=
      mul_le_mul hratio (stableRescaledJacobian_apply_bound hc hm hu hw w) (norm_nonneg _) (by positivity)
    _ = ((c + 1) / stableBoundaryDenom y) * (384 * (|y 1| + |y 2|) * ‖v‖ * ‖w‖) +
        ((c + 1) ^ 2 / stableBoundaryDenom y) * (216 * ‖v‖ * ‖![w 1, w 2]‖) := by ring
    _ ≤ 1 * (384 * (|y 1| + |y 2|) * ‖v‖ * ‖w‖) + 3 * (216 * ‖v‖ * ‖![w 1, w 2]‖) :=
      add_le_add (mul_le_mul_of_nonneg_right hs1 (by positivity))
        (mul_le_mul_of_nonneg_right hs2 (by positivity))
    _ = _ := by ring

theorem stableRescaledHessian_bound {y : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 10)
    (hu : |y 1| ≤ 1 / 100) (hw : |y 2| ≤ 1 / 100) (v w : StableState) :
    ‖(c + 1) • stableOriginalHessian y v w‖ ≤ 1024 * stableHessianBudget y v w := by
  let K := c + 1
  let D := stableBoundaryDenom y
  let b := |y 1| + |y 2|
  let R := b * ‖v‖ * ‖w‖
  let S := ‖![v 1, v 2]‖ * ‖w‖ + ‖v‖ * ‖![w 1, w 2]‖
  let T0 := (6 * K / D) • stableBoundaryHessian y v w
  let T1 := (dotProduct (stableDenomGradient y) v / D) • (K • (stableOriginalJacobian y).mulVec w)
  let T2 := (dotProduct (stableDenomGradient y) w / D) • (K • (stableOriginalJacobian y).mulVec v)
  let T3 := (stableDenomHessian v w / D) • (K • stableOriginalField y)
  have hD : 0 < D := stableBoundaryDenom_pos y
  have hK : 0 < K := by dsimp [K]; linarith
  have hs1 : K / D ≤ 1 := (div_le_one hD).mpr (stableBoundaryDenom_lower hc hm).2
  have hs2 : K ^ 2 / D ≤ 3 := (div_le_iff₀ hD).mpr (by nlinarith [(stableBoundaryDenom_lower hc hm).1])
  have hR : 0 ≤ R := by dsimp [R, b]; positivity
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hT0 : ‖T0‖ ≤ 6 * R + 216 * S := by
    dsimp only [T0]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 6 * K / D)]
    have H := mul_le_mul_of_nonneg_left (stableBoundaryHessian_mixed_bound hc hm hu hw v w)
      (show 0 ≤ 6 * K / D by positivity)
    calc
      _ ≤ (6 * K / D) * (R + 12 * K * S) := H
      _ = (K / D) * (6 * R) + (K ^ 2 / D) * (72 * S) := by ring
      _ ≤ 1 * (6 * R) + 3 * (72 * S) :=
        add_le_add (mul_le_mul_of_nonneg_right hs1 (by positivity))
          (mul_le_mul_of_nonneg_right hs2 (by positivity))
      _ = _ := by ring
  have hT1 := stableHessian_clock_term_bound hc hm hu hw v w
  have hT2 := stableHessian_clock_term_bound hc hm hu hw w v
  have hT3 : ‖T3‖ ≤ 60 * R := by
    dsimp only [T3]
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hK,
      abs_div, abs_of_pos hD]
    have H := mul_le_mul (stableDenomHessian_bound v w) (stableOriginalField_norm_bound hc hm hu hw)
      (norm_nonneg _) (by positivity)
    calc
      _ = (K / D) * (|stableDenomHessian v w| * ‖stableOriginalField y‖) := by ring
      _ ≤ 1 * ((10 * ‖v‖ * ‖w‖) * (6 * b)) :=
        mul_le_mul hs1 H (by positivity) (by norm_num)
      _ = 60 * R := by dsimp [R]; ring
  have heq : K • stableOriginalHessian y v w = T0 - T1 - T2 - T3 := by
    rw [stableOriginalHessian_factor]
    ext i
    dsimp [T0, T1, T2, T3, K, D]
    ring
  have H1 := norm_sub_le T0 T1
  have H2 := norm_sub_le (T0 - T1) T2
  have H3 := norm_sub_le (T0 - T1 - T2) T3
  change ‖K • stableOriginalHessian y v w‖ ≤ _
  rw [heq]
  change ‖T1‖ ≤ _ at hT1
  change ‖T2‖ ≤ _ at hT2
  dsimp [stableHessianBudget, R, S, b] at hT0 hT3 hR hS ⊢
  nlinarith only [H1, H2, H3, hT0, hT1, hT2, hT3, hR, hS]

end BianchiIX
