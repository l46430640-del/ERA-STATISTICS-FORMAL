import BianchiIX.Dynamics.StableClockStableVariation
import BianchiIX.Analysis.CoreIntegrals
import BianchiIX.Dynamics.StableHessianPolynomialBounds

noncomputable section

namespace BianchiIX

open Set MeasureTheory

def stableClockCenterBudget (y v : StableState) : ℝ :=
  4 * (|y 1| + |y 2|) * ‖![v 1, v 2]‖ +
    33 * (|y 1| + |y 2|) ^ 2 * Real.exp (32 * (|y 1| + |y 2|)) * ‖v‖

theorem stableClockCenterBudget_nonneg (y v : StableState) : 0 ≤ stableClockCenterBudget y v := by
  unfold stableClockCenterBudget
  positivity

theorem stableClockJacobian_center_apply {c : ℝ} {y v : StableState}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 10) :
    |(stableClockJacobian c y).mulVec v 0| ≤
      (|y 1| + |y 2|) ^ 2 * |v 0| + 4 * (|y 1| + |y 2|) * ‖![v 1, v 2]‖ := by
  have H := stableClockJacobian_center_bounds hc hm
  have hb : 0 ≤ |y 1| + |y 2| := by positivity
  have hK : 0 < c + 1 := by linarith
  have h0 : |stableClockJacobian c y 0 0| ≤ (|y 1| + |y 2|) ^ 2 :=
    H.1.trans ((div_le_iff₀ hK).mpr (by nlinarith [sq_nonneg (|y 1| + |y 2|)]))
  have hv1 : |v 1| ≤ ‖![v 1, v 2]‖ := by
    simpa only [Real.norm_eq_abs, Matrix.cons_val_zero] using norm_le_pi_norm ![v 1, v 2] 0
  have hv2 : |v 2| ≤ ‖![v 1, v 2]‖ := by
    simpa only [Real.norm_eq_abs, Matrix.cons_val_one, Matrix.cons_val_zero] using
      norm_le_pi_norm ![v 1, v 2] 1
  have he : (stableClockJacobian c y).mulVec v 0 =
      stableClockJacobian c y 0 0 * v 0 +
        (stableClockJacobian c y 0 1 * v 1 + stableClockJacobian c y 0 2 * v 2) := by
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  rw [he]
  have ht := (abs_add_le (stableClockJacobian c y 0 0 * v 0)
    (stableClockJacobian c y 0 1 * v 1 + stableClockJacobian c y 0 2 * v 2)).trans
      (add_le_add (le_refl _) (abs_add_le _ _))
  simp only [abs_mul] at ht
  have H0 := mul_le_mul_of_nonneg_right h0 (abs_nonneg (v 0))
  have H1 := mul_le_mul H.2.1 hv1 (abs_nonneg _) (by positivity)
  have H2 := mul_le_mul H.2.2 hv2 (abs_nonneg _) (by positivity)
  nlinarith only [ht, H0, H1, H2]

theorem stableClockFlow_center_variation_rate {c σ : ℝ} {y : StableState}
    (hc : 2 ≤ c) (hy : y ∈ stableParameterDomain c) (hσ : 0 ≤ σ) (v : StableState) :
    |(stableClockJacobian c (stableClockFlow c (y, σ))).mulVec
      (fderiv ℝ (stableClockFlow c) (y, σ) (v, 0)) 0| ≤
        stableClockCenterBudget y v * Real.exp (-σ / 4) := by
  let b := |y 1| + |y 2|
  let Y := stableClockFlow c (y, σ)
  let J := fderiv ℝ (stableClockFlow c) (y, σ) (v, 0)
  let B := |Y 1| + |Y 2|
  let M := Real.exp (32 * b) * ‖v‖
  let N := ‖![v 1, v 2]‖
  let e := Real.exp (-σ / 4)
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have he : 0 ≤ e := (Real.exp_pos _).le
  have he1 : e ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have H := stableClockJacobian_center_apply (v := J) hc (stableClockFlow_band hc hy hσ).1
  have hBe : B ≤ b * e := stableClockFlow_amplitude_decay hc hy hσ
  have hBb : B ≤ b := hBe.trans (mul_le_of_le_one_right hb he1)
  have hB2 : B ^ 2 ≤ b ^ 2 * e := by
    nlinarith only [mul_le_mul hBb hBe hB hb]
  have hJ0 : |J 0| ≤ M :=
    (show |J 0| ≤ ‖J‖ by simpa only [Real.norm_eq_abs] using norm_le_pi_norm J 0).trans
      (stableClockFlow_variation_bound hc hy hσ v)
  have hZ : ‖![J 1, J 2]‖ ≤ N + 8 * b * M := by
    have H' : ‖![J 1, J 2]‖ ≤ (N + 8 * b * M) * Real.exp (-σ / 8) := by
      convert! stableClockFlow_stable_variation_decay hc hy hσ v using 1
      dsimp [M, b, N]
      ring
    exact H'.trans (mul_le_of_le_one_right (by positivity)
      (Real.exp_le_one_iff.mpr (by linarith)))
  have H1 := mul_le_mul hB2 hJ0 (abs_nonneg _) (by positivity : 0 ≤ b ^ 2 * e)
  have H2 := mul_le_mul hBe hZ (norm_nonneg _) (mul_nonneg hb he)
  change |(stableClockJacobian c Y).mulVec J 0| ≤ B ^ 2 * |J 0| + 4 * B * ‖![J 1, J 2]‖ at H
  change |(stableClockJacobian c Y).mulVec J 0| ≤ stableClockCenterBudget y v * e
  have hout : |(stableClockJacobian c Y).mulVec J 0| ≤ (4 * b * N + 33 * b ^ 2 * M) * e := by
    nlinarith only [H, H1, H2]
  convert! hout using 1
  dsimp [stableClockCenterBudget, b, N, M]
  ring

theorem stableClockFlow_center_variation_tail {c a t : ℝ} {y : StableState}
    (hc : 2 ≤ c) (hy : y ∈ stableParameterDomain c) (ha : 0 ≤ a) (hat : a ≤ t) (v : StableState) :
    |fderiv ℝ (stableClockFlow c) (y, t) (v, 0) 0 -
      fderiv ℝ (stableClockFlow c) (y, a) (v, 0) 0| ≤
        4 * stableClockCenterBudget y v * Real.exp (-a / 4) := by
  let C := stableClockCenterBudget y v
  have hC : 0 ≤ C := stableClockCenterBudget_nonneg y v
  have hf (s : ℝ) (hs : s ∈ Icc a t) :=
    hasDerivAt_pi.mp (stableClockFlow_variational_equation hc hy (ha.trans hs.1) v) 0
  have hcont : Continuous (fun s : ℝ => C * Real.exp (-s / 4)) := by fun_prop
  have H := abs_sub_le_integral_bound hat hf hcont.continuousOn
    (fun s hs => stableClockFlow_center_variation_rate hc hy (ha.trans hs.1) v)
  have HI := integral_le_of_exp_decay (f := fun s : ℝ => C * Real.exp (-s / 4))
    (B := C * Real.exp (-a / 4)) (c := (1 / 4 : ℝ)) hat (by norm_num)
    (by positivity) hcont.continuousOn (fun s _ => ?_)
  · exact H.trans (by convert! HI using 1; ring)
  · have he : C * Real.exp (-s / 4) =
        (C * Real.exp (-a / 4)) * Real.exp (-(1 / 4) * (s - a)) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring
    exact he.le

theorem stableClockFlow_center_variation_drift {c σ : ℝ} {y : StableState}
    (hc : 2 ≤ c) (hy : y ∈ stableParameterDomain c) (hσ : 0 ≤ σ) (v : StableState) :
    |fderiv ℝ (stableClockFlow c) (y, σ) (v, 0) 0 - v 0| ≤
      4 * stableClockCenterBudget y v := by
  simpa only [stableClockFlow_variation_initial hc hy, neg_zero, zero_div,
    Real.exp_zero, mul_one] using stableClockFlow_center_variation_tail hc hy (le_refl 0) hσ v

theorem stableClockFlow_center_variation_bound {c σ : ℝ} {y : StableState}
    (hc : 2 ≤ c) (hy : y ∈ stableParameterDomain c) (hσ : 0 ≤ σ) (v : StableState) :
    |fderiv ℝ (stableClockFlow c) (y, σ) (v, 0) 0| ≤
      |v 0| + 18 * (|y 1| + |y 2|) * Real.exp (32 * (|y 1| + |y 2|)) * ‖v‖ := by
  let b := |y 1| + |y 2|
  let E := Real.exp (32 * b)
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hb1 : b ≤ 1 / 100 := by dsimp [b]; linarith [hy.2.1, hy.2.2]
  have hE : 1 ≤ E := Real.one_le_exp (by positivity)
  have H1 := mul_le_mul_of_nonneg_left (stableTangent_split_bounds v).2.2 hb
  have H2 := mul_le_mul_of_nonneg_right hE (show 0 ≤ b * ‖v‖ by positivity)
  have H3 := mul_le_mul_of_nonneg_right hb1 (show 0 ≤ b * E * ‖v‖ by positivity)
  have H := stableClockFlow_center_variation_drift hc hy hσ v
  have H' := abs_sub_abs_le_abs_sub (fderiv ℝ (stableClockFlow c) (y, σ) (v, 0) 0) (v 0)
  change |fderiv ℝ (stableClockFlow c) (y, σ) (v, 0) 0 - v 0| ≤
    4 * (4 * b * ‖![v 1, v 2]‖ + 33 * b ^ 2 * E * ‖v‖) at H
  change _ ≤ |v 0| + 18 * b * E * ‖v‖
  nlinarith only [H, H', H1, H2, H3,
    mul_nonneg hb (mul_nonneg (Real.exp_pos (32 * b)).le (norm_nonneg v))]

end BianchiIX
