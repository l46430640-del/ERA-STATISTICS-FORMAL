import BianchiIX.Dynamics.StableClockStrongInputs
import BianchiIX.Dynamics.StableSecondInputBounds

noncomputable section

namespace BianchiIX

theorem contDiffAt_stableClockFlow_slice {c s : ℝ} {y : StableState}
    (hc : 2 ≤ c) (hy : y ∈ stableParameterDomain c) (hs : 0 ≤ s) :
    ContDiffAt ℝ 2 (fun z => stableClockFlow c (z, s)) y :=
  (contDiffAt_stableClockFlow_two hc hy hs).comp y
    (f := fun z : StableState => (z, s)) (contDiffAt_id.prodMk contDiffAt_const)

theorem stableClockFlow_slice_fderiv {c s : ℝ} {y : StableState}
    (hc : 2 ≤ c) (hy : y ∈ stableParameterDomain c) (hs : 0 ≤ s) (v : StableState) :
    fderiv ℝ (fun z => stableClockFlow c (z, s)) y v =
      fderiv ℝ (stableClockFlow c) (y, s) (v, 0) :=
  fderiv_parameterSlice_apply ((contDiffAt_stableClockFlow_two hc hy hs).differentiableAt (by norm_num)) v

theorem stableClockFlow_residual_weights {c s : ℝ} {y : StableState}
    (hc : 2 ≤ c) (hy : y ∈ stableParameterDomain c) (hs : 0 ≤ s) :
    |stableClockFlow c (y, s) 1| + |stableClockFlow c (y, s) 2| ≤ |y 1| + |y 2| ∧
      |stableClockFlow c (y, s) 1| ≤ |y 1| * Real.exp (-(c + 1) / 16 * s) := by
  refine ⟨add_le_add (stableClockFlow_band hc hy hs).2.1 (stableClockFlow_band hc hy hs).2.2, ?_⟩
  exact (stableClockFlow_wall_decay hc hy hs).1.trans
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) (abs_nonneg _))

theorem stableClockFlow_first_residual_weights {c s : ℝ} {y : StableState}
    (hc : 2 ≤ c) (hy : y ∈ stableParameterDomain c) (hs : 0 ≤ s) (v : StableState) :
    let b := |y 1| + |y 2|
    let E := Real.exp 1
    let J := fderiv ℝ (fun z => stableClockFlow c (z, s)) y v
    ‖J‖ ≤ E * ‖v‖ ∧ ‖![J 1, J 2]‖ ≤ 256 * E * stableFirstInputWeight b v ∧
      |J 1| ≤ 200 * E * stableFirstInputWeight b v * Real.exp (-(c + 1) / 16 * s) := by
  dsimp only
  rw [stableClockFlow_slice_fderiv hc hy hs]
  let b := |y 1| + |y 2|
  let E := Real.exp 1
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hE : 1 ≤ E := Real.one_le_exp (by norm_num)
  have hA := stableFirstInputWeight_nonneg hb v
  have hEa : Real.exp (32 * b) ≤ E :=
    (stableClockFlow_variation_factor_le hy).trans (Real.exp_le_exp.mpr (by norm_num))
  refine ⟨(stableClockFlow_variation_bound hc hy hs v).trans
    (mul_le_mul_of_nonneg_right hEa (norm_nonneg v)), ?_, ?_⟩
  · have H := (stableClockFlow_stable_variation_weighted hc hy hs v).trans
      (mul_le_of_le_one_right (by positivity) (Real.exp_le_one_iff.mpr (by linarith)))
    have H' := mul_le_mul_of_nonneg_right hEa hA
    have hpos : 0 ≤ E * stableFirstInputWeight b v := by positivity
    nlinarith only [H, H', hpos]
  · have hv : |v 1| ≤ ‖![v 1, v 2]‖ := norm_le_pi_norm ![v 1, v 2] 0
    have hU : |y 1| ≤ b := le_add_of_nonneg_right (abs_nonneg _)
    have H0 := mul_le_mul_of_nonneg_right (mul_le_mul hU hEa (Real.exp_pos _).le hb) (norm_nonneg v)
    have H1 := mul_le_mul_of_nonneg_right hE (norm_nonneg (![v 1, v 2] : Fin 2 → ℝ))
    have hcoef : |v 1| + 16 * |y 1| * Real.exp (32 * b) * ‖v‖ ≤
        200 * E * stableFirstInputWeight b v := by
      unfold stableFirstInputWeight
      nlinarith only [hv, H0, H1, show 0 ≤ E * b * ‖v‖ by positivity,
        show 0 ≤ E * ‖![v 1, v 2]‖ by positivity]
    exact (stableClockFlow_strong_variation_budget hc hy hs v).trans
      (mul_le_mul_of_nonneg_right hcoef (Real.exp_pos _).le)

theorem stableClockFlow_second_residual_weights {c s : ℝ} {y : StableState}
    (hc : 2 ≤ c) (hy : y ∈ stableParameterDomain c) (hs : 0 ≤ s) (v w : StableState) :
    let b := |y 1| + |y 2|
    let E := Real.exp 1
    let H := fderiv ℝ (fderiv ℝ (fun z => stableClockFlow c (z, s))) y v w
    ‖H‖ ≤ 2400000 * E ^ 3 * stableSecondInputWeight b v w ∧
      |H 1| ≤ 320000000 * E ^ 3 * stableSecondInputWeight b v w * Real.exp (-(c + 1) / 16 * s) := by
  dsimp only
  let b := |y 1| + |y 2|
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hW := stableSecondInputWeight_nonneg hb v w
  have hEa := pow_le_pow_left₀ (Real.exp_pos _).le
    ((stableClockFlow_variation_factor_le hy).trans (Real.exp_le_exp.mpr (by norm_num : (8 / 25 : ℝ) ≤ 1))) 3
  constructor
  · have H := stableClockFlow_second_variation_bound hc hy hs v w
    nlinarith only [H, mul_le_mul_of_nonneg_right hEa hW,
      show 0 ≤ Real.exp 1 ^ 3 * stableSecondInputWeight b v w by positivity]
  · have hbudget := stableStrongHessianBudget_input_bound
      (by linarith [hy.2.1, hy.2.2] : |y 1| + |y 2| ≤ 1) v w
    have hprod := mul_le_mul hEa hbudget (stableStrongHessianBudget_nonneg y v w) (by positivity)
    have hdiv := div_le_self
      (show 0 ≤ 560000 * Real.exp (32 * b) ^ 3 * stableStrongHessianBudget y v w by
        have := stableStrongHessianBudget_nonneg y v w
        positivity) (show 1 ≤ c + 1 by linarith)
    have hcoef : 560000 * Real.exp (32 * b) ^ 3 * stableStrongHessianBudget y v w / (c + 1) ≤
        320000000 * Real.exp 1 ^ 3 * stableSecondInputWeight b v w := by
      nlinarith only [hdiv, hprod, show 0 ≤ Real.exp 1 ^ 3 * stableSecondInputWeight b v w by positivity]
    exact (stableClockFlow_strong_second_variation_decay hc hy hs v w).trans
      (mul_le_mul_of_nonneg_right hcoef (Real.exp_pos _).le)

end BianchiIX
