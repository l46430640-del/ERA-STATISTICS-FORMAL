import BianchiIX.Dynamics.StableClockHessian

noncomputable section

namespace BianchiIX

theorem stableStrongHessianBudget_controls_product {y : StableState}
    (hb : |y 1| + |y 2| ≤ 1) (v w : StableState) :
    (|y 1| + |y 2|) * stableStrongHessianBudget y v w ≤
      2 * stableFirstInputWeight (|y 1| + |y 2|) v *
        stableFirstInputWeight (|y 1| + |y 2|) w := by
  let b := |y 1| + |y 2|
  let V := ‖v‖
  let W := ‖w‖
  let N := ‖![v 1, v 2]‖
  let P := ‖![w 1, w 2]‖
  have hb0 : 0 ≤ b := by dsimp [b]; positivity
  have hv0 : |v 0| ≤ V := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm v 0
  have hw0 : |w 0| ≤ W := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm w 0
  have hv1 : |v 1| ≤ N := by
    simpa only [Real.norm_eq_abs, Matrix.cons_val_zero] using norm_le_pi_norm ![v 1, v 2] 0
  have hw1 : |w 1| ≤ P := by
    simpa only [Real.norm_eq_abs, Matrix.cons_val_zero] using norm_le_pi_norm ![w 1, w 2] 0
  have HT : |v 0| * |w 1| + |v 1| * |w 0| ≤ V * P + N * W :=
    add_le_add (mul_le_mul hv0 hw1 (abs_nonneg _) (norm_nonneg _))
      (mul_le_mul hv1 hw0 (abs_nonneg _) (norm_nonneg _))
  have HS : |v 1| * W + V * |w 1| ≤ V * P + N * W := by
    nlinarith only [mul_le_mul_of_nonneg_right hv1 (norm_nonneg w),
      mul_le_mul_of_nonneg_left hw1 (norm_nonneg v)]
  have HR := mul_le_mul_of_nonneg_right (show |y 1| ≤ b by dsimp [b]; linarith [abs_nonneg (y 2)])
    (show 0 ≤ b * V * W by positivity)
  have H1 := mul_le_mul_of_nonneg_left HT hb0
  have H2 := mul_le_mul_of_nonneg_left HS (sq_nonneg b)
  have H3 := mul_le_mul_of_nonneg_right hb (show 0 ≤ b * (V * P + N * W) by positivity)
  change b * stableStrongHessianBudget y v w ≤ 2 * (b * V + N) * (b * W + P)
  unfold stableStrongHessianBudget
  nlinarith only [HR, H1, H2, H3, show 0 ≤ b ^ 2 * V * W by positivity,
    show 0 ≤ N * P by positivity]

theorem stableStrongHessianBudget_controls_input {y : StableState}
    (hb : |y 1| + |y 2| ≤ 1) (v w : StableState) :
    |y 1| * stableSecondInputWeight (|y 1| + |y 2|) v w ≤
      3 * stableStrongHessianBudget y v w := by
  have H0 := mul_le_mul_of_nonneg_right hb (show 0 ≤ ‖v‖ * ‖w‖ by positivity)
  have H1 := mul_le_mul_of_nonneg_right (stableTangent_split_bounds v).2.2 (norm_nonneg w)
  have H2 := mul_le_mul_of_nonneg_left (stableTangent_split_bounds w).2.2 (norm_nonneg v)
  have H : stableSecondInputWeight (|y 1| + |y 2|) v w ≤ 3 * ‖v‖ * ‖w‖ := by
    unfold stableSecondInputWeight
    nlinarith only [H0, H1, H2]
  have H' := mul_le_mul_of_nonneg_left H (abs_nonneg (y 1))
  unfold stableStrongHessianBudget
  nlinarith only [H', show 0 ≤ |v 0| * |w 1| + |v 1| * |w 0| by positivity,
    show 0 ≤ (|y 1| + |y 2|) * (|v 1| * ‖w‖ + ‖v‖ * |w 1|) by positivity]

theorem stableClockFlow_strong_second_forcing_decay {c σ : ℝ} {y : StableState}
    (hc : 2 ≤ c) (hy : y ∈ stableParameterDomain c) (hσ : 0 ≤ σ) (v w : StableState) :
    |fderiv ℝ (fderiv ℝ (stableClockField c)) (stableClockFlow c (y, σ))
      (fderiv ℝ (stableClockFlow c) (y, σ) (v, 0))
      (fderiv ℝ (stableClockFlow c) (y, σ) (w, 0)) 1| ≤
        25000 * Real.exp (32 * (|y 1| + |y 2|)) ^ 2 * stableStrongHessianBudget y v w *
          Real.exp (-(c + 1) / 16 * σ) := by
  let E := Real.exp (32 * (|y 1| + |y 2|))
  let q := Real.exp (-(c + 1) / 16 * σ)
  let Y := stableClockFlow c (y, σ)
  let J := fun a => fderiv ℝ (stableClockFlow c) (y, σ) (a, 0)
  have hE : 1 ≤ E := Real.one_le_exp (by positivity)
  have hq : 0 ≤ q := (Real.exp_pos _).le
  have hnorm (a : StableState) : ‖J a‖ ≤ E * ‖a‖ := stableClockFlow_variation_bound hc hy hσ a
  have hcenter (a : StableState) : |J a 0| ≤
      |a 0| + 1000 * (|y 1| + |y 2|) * E * ‖a‖ := by
    have H := stableClockFlow_center_variation_bound hc hy hσ a
    have hn : 0 ≤ (|y 1| + |y 2|) * E * ‖a‖ := by positivity
    nlinarith only [H, hn]
  have hstrong (a : StableState) : |J a 1| ≤ (|a 1| + 200 * |y 1| * E * ‖a‖) * q := by
    have H := stableClockFlow_strong_variation_budget hc hy hσ a
    have hn : 0 ≤ |y 1| * E * ‖a‖ * q := by positivity
    nlinarith only [H, hn]
  have hY : |Y 1| + |Y 2| ≤ |y 1| + |y 2| :=
    add_le_add (stableClockFlow_band hc hy hσ).2.1 (stableClockFlow_band hc hy hσ).2.2
  have hU : |Y 1| ≤ |y 1| * q := (stableClockFlow_wall_decay hc hy hσ).1.trans
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) (abs_nonneg (y 1)))
  have H := stableStrongHessianBudget_transport hE hq hy.2.1.le hy.2.2.le
    (hnorm v) (hnorm w) (hcenter v) (hcenter w) (hstrong v) (hstrong w) hU hY
  have HF := stableClockField_strong_hessian_bound hc (stableClockFlow_band hc hy hσ).1 (J v) (J w)
  nlinarith only [HF, H]

end BianchiIX
