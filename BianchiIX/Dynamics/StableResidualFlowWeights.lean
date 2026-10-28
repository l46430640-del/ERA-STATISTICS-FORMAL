import BianchiIX.Dynamics.StableSecondInputBounds

noncomputable section

namespace BianchiIX

theorem stableSmallAmplitude_exp_bound {y : StableState}
    (hu : |y 1| ≤ 1 / 200) (hw : |y 2| ≤ 1 / 200) :
    Real.exp (512 * (|y 1| + |y 2|)) ≤ Real.exp 6 :=
  Real.exp_le_exp.mpr (by linarith)

theorem stableRescaledFlow_residual_weights {y : StableState} {c s : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 40)
    (hu : |y 1| ≤ 1 / 200) (hw : |y 2| ≤ 1 / 200) (hs : 0 ≤ s) :
    |stableRescaledFlow (c + 1) y s 1| + |stableRescaledFlow (c + 1) y s 2| ≤ |y 1| + |y 2| ∧
      |stableRescaledFlow (c + 1) y s 1| ≤ |y 1| * Real.exp (-(c + 1) / 16 * s) := by
  constructor
  · exact (stableRescaledFlow_amplitude_decay hc hm hu hw hs).trans
      ((mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr (by linarith))
        (by positivity : 0 ≤ |y 1| + |y 2|)).trans_eq (mul_one _))
  · exact (stableRescaledFlow_wall_decay hc hm hu hw hs).1.trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) (abs_nonneg _))

theorem stableRescaledDifferential_residual_weights {y : StableState} {c s : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 40)
    (hu : |y 1| ≤ 1 / 200) (hw : |y 2| ≤ 1 / 200) (hs : 0 ≤ s) (v : StableState) :
    let b := |y 1| + |y 2|
    let E := Real.exp 6
    let J := stableRescaledDifferential (c + 1) y s v
    ‖J‖ ≤ E * ‖v‖ ∧ ‖![J 1, J 2]‖ ≤ 256 * E * stableFirstInputWeight b v ∧
      |J 1| ≤ 200 * E * stableFirstInputWeight b v * Real.exp (-(c + 1) / 16 * s) := by
  dsimp only
  let b := |y 1| + |y 2|
  let E := Real.exp 6
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hE : 1 ≤ E := Real.one_le_exp_iff.mpr (by norm_num)
  have hE0 : 0 ≤ E := le_trans (by norm_num) hE
  have hA := stableFirstInputWeight_nonneg hb v
  have hEa := stableSmallAmplitude_exp_bound hu hw
  have hnorm := (stableRescaledDifferential_bound hc hm hu hw hs v).trans
    (mul_le_mul_of_nonneg_right hEa (norm_nonneg v))
  refine ⟨hnorm, ?_, ?_⟩
  · have H := (stableRescaledDifferential_stable_decay hc hm hu hw hs v).trans
      ((mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr (by linarith)) (by positivity)).trans_eq (mul_one _))
    have T0 := mul_le_mul_of_nonneg_left hEa (show 0 ≤ 256 * b * ‖v‖ by positivity)
    have T1 := mul_le_mul_of_nonneg_right hE (norm_nonneg (![v 1, v 2] : Fin 2 → ℝ))
    have T2 : 0 ≤ E * ‖![v 1, v 2]‖ := by positivity
    change _ ≤ 256 * E * stableFirstInputWeight b v
    dsimp only [b] at T0
    unfold stableFirstInputWeight
    dsimp only [b, E] at T1 T2 ⊢
    nlinarith only [H, T0, T1, T2]
  · have hv1 : |v 1| ≤ ‖![v 1, v 2]‖ := norm_le_pi_norm ![v 1, v 2] 0
    have hU : |y 1| ≤ b := le_add_of_nonneg_right (abs_nonneg _)
    have T0 := mul_le_mul_of_nonneg_right
      (mul_le_mul hU hEa (Real.exp_pos _).le hb) (norm_nonneg v)
    have T1 := mul_le_mul_of_nonneg_right hE (norm_nonneg (![v 1, v 2] : Fin 2 → ℝ))
    have T2 : 0 ≤ E * ‖![v 1, v 2]‖ := by positivity
    have hcoef : |v 1| + 200 * |y 1| * Real.exp (512 * b) * ‖v‖ ≤
        200 * E * stableFirstInputWeight b v := by
      unfold stableFirstInputWeight
      dsimp only [b, E] at T0 T1 T2 ⊢
      nlinarith only [hv1, T0, T1, T2]
    exact (stableRescaledDifferential_strong_budget hc hm hu hw hs v).trans
      (mul_le_mul hcoef (Real.exp_le_exp.mpr (by nlinarith)) (Real.exp_pos _).le (by positivity))

theorem stableRescaledSecondDifferential_residual_weights {y : StableState} {c s : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| < 1 / 40)
    (hu : |y 1| < 1 / 200) (hw : |y 2| < 1 / 200) (hs : 0 ≤ s) (v w : StableState) :
    let b := |y 1| + |y 2|
    let E := Real.exp 6
    let H := stableRescaledSecondDifferential (c + 1) y s v w
    ‖H‖ ≤ 2400000 * E ^ 3 * stableSecondInputWeight b v w ∧
      |H 1| ≤ 320000000 * E ^ 3 * stableSecondInputWeight b v w * Real.exp (-(c + 1) / 16 * s) := by
  dsimp only
  let b := |y 1| + |y 2|
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hW := stableSecondInputWeight_nonneg hb v w
  have hEa := pow_le_pow_left₀ (Real.exp_pos _).le (stableSmallAmplitude_exp_bound hu.le hw.le) 3
  constructor
  · exact (stableRescaledSecondDifferential_input_bound hc hm hu hw hs v w).trans
      (by nlinarith only [mul_le_mul_of_nonneg_right hEa hW])
  · have hK1 : 1 ≤ c + 1 := by linarith
    have hbudget := stableStrongHessianBudget_input_bound (by linarith : |y 1| + |y 2| ≤ 1) v w
    have hbudget0 := stableStrongHessianBudget_nonneg y v w
    have hprod := mul_le_mul hEa hbudget (stableStrongHessianBudget_nonneg y v w) (by positivity)
    have hdiv := div_le_self (show 0 ≤ 160000000 * Real.exp (512 * b) ^ 3 * stableStrongHessianBudget y v w by positivity) hK1
    have hcoef : 160000000 * Real.exp (512 * b) ^ 3 * stableStrongHessianBudget y v w / (c + 1) ≤
        320000000 * Real.exp 6 ^ 3 * stableSecondInputWeight b v w := by
      dsimp only [b] at hdiv ⊢
      nlinarith only [hdiv, hprod]
    exact (stableRescaledSecondDifferential_strong_decay hc hm hu hw hs v w).trans
      (mul_le_mul hcoef (Real.exp_le_exp.mpr (by nlinarith)) (Real.exp_pos _).le (by positivity))

end BianchiIX
