import BianchiIX.Dynamics.StableClockInputBounds
import BianchiIX.Dynamics.StableStrongVariationBudgets

noncomputable section

namespace BianchiIX

theorem stableClockField_fderiv2 (c : ℝ) (y v w : StableState) :
    fderiv ℝ (fderiv ℝ (stableClockField c)) y v w =
      (c + 1)⁻¹ • stableBoundaryHessian y v w := by
  have hl : HasDerivAt (fun s : ℝ => y + s • v) v 0 := by
    convert! (hasDerivAt_const (0 : ℝ) y).add ((hasDerivAt_id (0 : ℝ)).smul_const v) using 1
    simp
  have hD : Differentiable ℝ (fderiv ℝ (stableClockField c)) :=
    ((contDiff_stableClockField c 2).fderiv_right
      (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiable (by norm_num)
  have H := hasDerivAt_fderiv_apply_const (hD (y + (0 : ℝ) • v)) hl w
  simp only [stableClockField_fderiv] at H
  simpa only [zero_smul, add_zero] using
    H.unique ((hasDerivAt_stableBoundaryJacobian_mulVec hl w).const_smul ((c + 1)⁻¹))

theorem stableClockField_hessian_bound {c : ℝ} {y : StableState}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 10)
    (hu : |y 1| ≤ 1 / 100) (hw : |y 2| ≤ 1 / 100) (v w : StableState) :
    ‖fderiv ℝ (fderiv ℝ (stableClockField c)) y v w‖ ≤
      12 * stableSecondInputWeight (|y 1| + |y 2|) v w := by
  have hK : 0 < c + 1 := by linarith
  rw [stableClockField_fderiv2, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hK)]
  have H := mul_le_mul_of_nonneg_left (stableBoundaryHessian_mixed_bound hc hm hu hw v w)
    (inv_nonneg.mpr hK.le)
  have hR : 0 ≤ (|y 1| + |y 2|) * ‖v‖ * ‖w‖ := by positivity
  have hInv : (c + 1)⁻¹ ≤ 1 := (inv_le_one₀ hK).mpr (by linarith)
  have H' := mul_le_mul_of_nonneg_right hInv hR
  have he : (c + 1)⁻¹ * (12 * (c + 1) *
      (‖![v 1, v 2]‖ * ‖w‖ + ‖v‖ * ‖![w 1, w 2]‖)) =
      12 * (‖![v 1, v 2]‖ * ‖w‖ + ‖v‖ * ‖![w 1, w 2]‖) := by field_simp
  unfold stableSecondInputWeight
  nlinarith only [H, H', he, hR]

theorem stableClockField_strong_hessian_bound {c : ℝ} {y : StableState}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 10) (v w : StableState) :
    |fderiv ℝ (fderiv ℝ (stableClockField c)) y v w 1| ≤
      5 * stableStrongHessianBudget y v w := by
  have hK : 0 < c + 1 := by linarith
  rw [stableClockField_fderiv2]
  change |(c + 1)⁻¹ * stableBoundaryHessian y v w 1| ≤ _
  rw [abs_mul, abs_of_pos (inv_pos.mpr hK)]
  have H := mul_le_mul_of_nonneg_left (stableBoundaryHessian_strong_bound hc hm v w)
    (inv_nonneg.mpr hK.le)
  let R := |y 1| * ‖v‖ * ‖w‖
  let S := (|y 1| + |y 2|) * (|v 1| * ‖w‖ + ‖v‖ * |w 1|)
  let T := |v 0| * |w 1| + |v 1| * |w 0|
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hInv : (c + 1)⁻¹ ≤ 1 := (inv_le_one₀ hK).mpr (by linarith)
  have H1 := mul_le_mul_of_nonneg_right hInv hR
  have H2 := mul_le_mul_of_nonneg_right hInv hS
  have he : (c + 1)⁻¹ * ((c + 1) * T) = T := by field_simp
  dsimp only [R, S, T] at H1 H2 he hT hS
  unfold stableStrongHessianBudget
  nlinarith only [H, H1, H2, he, hT, hS]

theorem stableClockFlow_second_forcing_decay {c σ : ℝ} {y : StableState}
    (hc : 2 ≤ c) (hy : y ∈ stableParameterDomain c) (hσ : 0 ≤ σ) (v w : StableState) :
    ‖fderiv ℝ (fderiv ℝ (stableClockField c)) (stableClockFlow c (y, σ))
      (fderiv ℝ (stableClockFlow c) (y, σ) (v, 0))
      (fderiv ℝ (stableClockFlow c) (y, σ) (w, 0))‖ ≤
        204 * Real.exp (32 * (|y 1| + |y 2|)) ^ 2 *
          stableSecondInputWeight (|y 1| + |y 2|) v w * Real.exp (-σ / 8) := by
  let b := |y 1| + |y 2|
  let E := Real.exp (32 * b)
  let Jv := fderiv ℝ (stableClockFlow c) (y, σ) (v, 0)
  let Jw := fderiv ℝ (stableClockFlow c) (y, σ) (w, 0)
  let Y := stableClockFlow c (y, σ)
  let e := Real.exp (-σ / 8)
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hE : 0 ≤ E := (Real.exp_pos _).le
  have he : 0 ≤ e := (Real.exp_pos _).le
  have hY : |Y 1| + |Y 2| ≤ b * e :=
    (stableClockFlow_amplitude_decay hc hy hσ).trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hb)
  have hJv := stableClockFlow_variation_bound hc hy hσ v
  have hJw := stableClockFlow_variation_bound hc hy hσ w
  have hZv := stableClockFlow_stable_variation_weighted hc hy hσ v
  have hZw := stableClockFlow_stable_variation_weighted hc hy hσ w
  have hIv := stableFirstInputWeight_nonneg hb v
  have hIw := stableFirstInputWeight_nonneg hb w
  have H0 := mul_le_mul (mul_le_mul hY hJv (norm_nonneg _) (by positivity))
    hJw (norm_nonneg _) (by positivity)
  have H1 := mul_le_mul hZv hJw (norm_nonneg _) (by positivity)
  have H2 := mul_le_mul hJv hZw (norm_nonneg _) (by positivity)
  obtain ⟨hm, hu, hw⟩ := stableClockFlow_band hc hy hσ
  have H := stableClockField_hessian_bound hc hm
    (hu.trans (by linarith [hy.2.1])) (hw.trans (by linarith [hy.2.2])) Jv Jw
  have hN : 0 ≤ E ^ 2 * (‖![v 1, v 2]‖ * ‖w‖ + ‖v‖ * ‖![w 1, w 2]‖) * e := by positivity
  change _ ≤ 204 * E ^ 2 * stableSecondInputWeight b v w * e
  dsimp only [stableFirstInputWeight] at H1 H2
  dsimp only [stableSecondInputWeight] at H ⊢
  nlinarith only [H, H0, H1, H2, hN]

end BianchiIX
