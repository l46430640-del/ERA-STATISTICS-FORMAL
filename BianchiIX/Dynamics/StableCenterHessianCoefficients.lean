import BianchiIX.Dynamics.StableHessianBounds
import BianchiIX.Dynamics.StableBoundaryCenterVariation

noncomputable section

namespace BianchiIX

theorem stableBoundaryHessian_center_bound {y : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 10) (v w : StableState) :
    |stableBoundaryHessian y v w 0| ≤
      3 * (|y 1| + |y 2|) * (‖v‖ * ‖![w 1, w 2]‖ + ‖![v 1, v 2]‖ * ‖w‖) +
        8 * (c + 1) * ‖![v 1, v 2]‖ * ‖![w 1, w 2]‖ := by
  let K := c + 1
  let b := |y 1| + |y 2|
  let S := ‖v‖ * ‖![w 1, w 2]‖ + ‖![v 1, v 2]‖ * ‖w‖
  let R := ‖![v 1, v 2]‖ * ‖![w 1, w 2]‖
  obtain ⟨_, _, hm0, hmK, hm1, hm1K⟩ := stable_boundary_band hc hm
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hz (a : StableState) (i : Fin 3) (hi : i ≠ 0) : |a i| ≤ ‖![a 1, a 2]‖ := by
    fin_cases i
    · exact (hi rfl).elim
    · change |a 1| ≤ ‖![a 1, a 2]‖
      simpa only [Real.norm_eq_abs, Matrix.cons_val_zero] using norm_le_pi_norm ![a 1, a 2] 0
    · change |a 2| ≤ ‖![a 1, a 2]‖
      simpa only [Real.norm_eq_abs, Matrix.cons_val_one, Matrix.cons_val_zero] using norm_le_pi_norm ![a 1, a 2] 1
  have h0 (a : StableState) : |a 0| ≤ ‖a‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm a 0
  have hcros (i : Fin 3) (hi : i ≠ 0) : |v 0 * w i + v i * w 0| ≤ S := by
    have H := abs_add_le (v 0 * w i) (v i * w 0)
    simp only [abs_mul] at H
    dsimp [S]
    nlinarith only [H, mul_le_mul (h0 v) (hz w i hi) (abs_nonneg _) (norm_nonneg _),
      mul_le_mul (hz v i hi) (h0 w) (abs_nonneg _) (norm_nonneg _)]
  have hp (i j : Fin 3) (hi : i ≠ 0) (hj : j ≠ 0) : |v i * w j| ≤ R := by
    rw [abs_mul]
    exact mul_le_mul (hz v i hi) (hz w j hj) (abs_nonneg _) (norm_nonneg _)
  have hcross : |v 1 * w 2 + v 2 * w 1| ≤ 2 * R :=
    (abs_add_le _ _).trans (by linarith [hp 1 2 (by decide) (by decide), hp 2 1 (by decide) (by decide)])
  have hcoef : |2 * y 1 - y 2| ≤ 2 * b := by
    have H := abs_sub (2 * y 1) (y 2)
    simp only [abs_mul] at H
    norm_num only at H
    dsimp [b]
    linarith [abs_nonneg (y 2)]
  have H1 := mul_le_mul hcoef (hcros 1 (by decide)) (abs_nonneg _) (by positivity)
  have H2 := mul_le_mul (show |y 1| ≤ b by dsimp [b]; linarith [abs_nonneg (y 2)])
    (hcros 2 (by decide)) (abs_nonneg _) hb
  have H3 := mul_le_mul (show |y 0| ≤ K by rwa [abs_of_nonneg hm0]) (hp 1 1 (by decide) (by decide))
    (abs_nonneg _) (by dsimp [K]; linarith)
  have H4 := mul_le_mul (show |y 0 + 1| ≤ 2 * K by rwa [abs_of_nonneg hm1]) hcross
    (abs_nonneg _) (by dsimp [K]; linarith)
  have H5 := hp 2 2 (by decide) (by decide)
  have H6 : R ≤ K * R := by dsimp [K]; nlinarith
  have htri (a b c d e : ℝ) : |a - b + c - d + e| ≤ |a| + |b| + |c| + |d| + |e| := by
    linarith only [abs_sub a b, abs_add_le (a - b) c, abs_sub (a - b + c) d, abs_add_le (a - b + c - d) e]
  have H := htri ((2 * y 1 - y 2) * (v 0 * w 1 + v 1 * w 0))
    (y 1 * (v 0 * w 2 + v 2 * w 0)) (2 * y 0 * v 1 * w 1)
    ((y 0 + 1) * (v 1 * w 2 + v 2 * w 1)) (2 * v 2 * w 2)
  change |stableBoundaryHessian y v w 0| ≤ _ at H
  simp only [abs_mul] at H H3 H5
  norm_num only at H
  have HB : |stableBoundaryHessian y v w 0| ≤ 3 * b * S + 8 * K * R := by
    nlinarith only [H, H1, H2, H3, H4, H5, H6]
  convert! HB using 1
  dsimp [b, S, K, R]
  ring

theorem stableOriginalField_center_bound {y : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 10) :
    |stableOriginalField y 0| ≤ 6 * (|y 1| + |y 2|) ^ 2 := by
  have H := mul_le_mul_of_nonneg_left (stableBoundary_phase_div_bound hc hm)
    (by norm_num : (0 : ℝ) ≤ 6)
  change |(6 / stableBoundaryDenom y) * stableBoundaryField y 0| ≤ _
  rw [show (6 / stableBoundaryDenom y) * stableBoundaryField y 0 =
    6 * (stableBoundaryField y 0 / stableBoundaryDenom y) by ring, abs_mul]
  norm_num only
  exact H

theorem stableCenterHessian_clock_bound {y : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 10)
    (hu : |y 1| ≤ 1 / 100) (hw : |y 2| ≤ 1 / 100) (v w : StableState) :
    |(dotProduct (stableDenomGradient y) v / stableBoundaryDenom y) *
        ((c + 1) * (stableOriginalJacobian y).mulVec w 0)| ≤
      384 * (|y 1| + |y 2|) ^ 2 * ‖v‖ * ‖w‖ +
        768 * (|y 1| + |y 2|) * ‖v‖ * ‖![w 1, w 2]‖ := by
  let K := c + 1
  let D := stableBoundaryDenom y
  let b := |y 1| + |y 2|
  have hD : 0 < D := stableBoundaryDenom_pos y
  have hK : 0 < K := by dsimp [K]; linarith
  have hscale : K / D ≤ 1 := (div_le_one hD).mpr (stableBoundaryDenom_lower hc hm).2
  have hratio : |dotProduct (stableDenomGradient y) v| / D ≤ (6 * K / D) * ‖v‖ := by
    convert! div_le_div_of_nonneg_right (stableDenomGradient_bound hc hm hu hw v) hD.le using 1
    ring
  have hw0 : |w 0| ≤ ‖w‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm w 0
  have hrow : |K * (stableOriginalJacobian y).mulVec w 0| ≤
      64 * b ^ 2 * ‖w‖ + 128 * b * ‖![w 1, w 2]‖ :=
    (stableRescaledJacobian_center_apply hc hm hu hw).trans
      (add_le_add (mul_le_mul_of_nonneg_left hw0 (by positivity)) (le_refl _))
  rw [abs_mul, abs_div, abs_of_pos hD]
  calc
    _ ≤ ((6 * K / D) * ‖v‖) * (64 * b ^ 2 * ‖w‖ + 128 * b * ‖![w 1, w 2]‖) :=
      mul_le_mul hratio hrow (abs_nonneg _) (by positivity)
    _ = (K / D) * (384 * b ^ 2 * ‖v‖ * ‖w‖ + 768 * b * ‖v‖ * ‖![w 1, w 2]‖) := by ring
    _ ≤ 1 * (384 * b ^ 2 * ‖v‖ * ‖w‖ + 768 * b * ‖v‖ * ‖![w 1, w 2]‖) :=
      mul_le_mul_of_nonneg_right hscale (by dsimp [b]; positivity)
    _ = _ := one_mul _

end BianchiIX
