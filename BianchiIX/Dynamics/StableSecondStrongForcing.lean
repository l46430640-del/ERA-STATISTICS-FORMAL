import BianchiIX.Dynamics.StableStrongVariationBudgets
import BianchiIX.Dynamics.StableSecondGrowth

noncomputable section

namespace BianchiIX

theorem stableSecondStrongForcing_decay {y : StableState} {c s : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 40)
    (hu : |y 1| ≤ 1 / 200) (hw : |y 2| ≤ 1 / 200) (hs : 0 ≤ s) (v w : StableState) :
    |((c + 1) • stableOriginalHessian (stableRescaledFlow (c + 1) y s)
        (stableRescaledDifferential (c + 1) y s v) (stableRescaledDifferential (c + 1) y s w)) 1| ≤
      10240000 * Real.exp (512 * (|y 1| + |y 2|)) ^ 2 * stableStrongHessianBudget y v w *
        Real.exp (-3 * (c + 1) / 16 * s) := by
  let E := Real.exp (512 * (|y 1| + |y 2|))
  let Y := stableRescaledFlow (c + 1) y s
  have hE : 1 ≤ E := Real.one_le_exp (by positivity)
  have hU : |Y 1| ≤ |y 1| * Real.exp (-3 * (c + 1) / 16 * s) :=
    (stableRescaledFlow_wall_decay hc hm hu hw hs).1.trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) (abs_nonneg _))
  have hb : |Y 1| + |Y 2| ≤ |y 1| + |y 2| :=
    (stableRescaledFlow_amplitude_decay hc hm hu hw hs).trans
      (mul_le_of_le_one_right (by positivity) (Real.exp_le_one_iff.mpr (by linarith)))
  have H := stableStrongHessianBudget_transport hE (Real.exp_pos _).le hu hw
    (stableRescaledDifferential_bound hc hm hu hw hs v)
    (stableRescaledDifferential_bound hc hm hu hw hs w)
    (stableRescaledDifferential_center_bound hc hm hu hw hs v)
    (stableRescaledDifferential_center_bound hc hm hu hw hs w)
    (stableRescaledDifferential_strong_budget hc hm hu hw hs v)
    (stableRescaledDifferential_strong_budget hc hm hu hw hs w) hU hb
  obtain ⟨hm', hu', hw'⟩ := stableRescaledFlow_band hc hm hu hw hs
  have H' := (stableRescaledHessian_strong_bound hc hm' hu' hw'
    (stableRescaledDifferential (c + 1) y s v) (stableRescaledDifferential (c + 1) y s w)).trans
      (mul_le_mul_of_nonneg_left H (by norm_num : (0 : ℝ) ≤ 2048))
  convert! H' using 1
  ring

theorem stableSecondStrongSource_offDiagonal {y : StableState} {c s : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| < 1 / 40)
    (hu : |y 1| < 1 / 200) (hw : |y 2| < 1 / 200) (hs : 0 ≤ s) (v w : StableState) :
    |(c + 1) * stableOriginalJacobian (stableRescaledFlow (c + 1) y s) 1 0 *
          stableRescaledSecondDifferential (c + 1) y s v w 0 +
      (c + 1) * stableOriginalJacobian (stableRescaledFlow (c + 1) y s) 1 2 *
          stableRescaledSecondDifferential (c + 1) y s v w 2 +
      ((c + 1) • stableOriginalHessian (stableRescaledFlow (c + 1) y s)
        (stableRescaledDifferential (c + 1) y s v) (stableRescaledDifferential (c + 1) y s w)) 1| ≤
      15000000 * Real.exp (512 * (|y 1| + |y 2|)) ^ 3 * stableStrongHessianBudget y v w *
        Real.exp (-3 * (c + 1) / 16 * s) := by
  let E := Real.exp (512 * (|y 1| + |y 2|))
  let Y := stableRescaledFlow (c + 1) y s
  let H := stableRescaledSecondDifferential (c + 1) y s v w
  let B := stableStrongHessianBudget y v w
  let q := Real.exp (-3 * (c + 1) / 16 * s)
  have hE : 1 ≤ E := Real.one_le_exp (by positivity)
  have hB : 0 ≤ B := stableStrongHessianBudget_nonneg y v w
  have hq : 0 ≤ q := (Real.exp_pos _).le
  have hB0 : |y 1| * ‖v‖ * ‖w‖ ≤ B := by
    have H : 0 ≤ (|v 0| * |w 1| + |v 1| * |w 0|) +
        (|y 1| + |y 2|) * (|v 1| * ‖w‖ + ‖v‖ * |w 1|) := by positivity
    dsimp [B, stableStrongHessianBudget]
    linarith
  have hU : |Y 1| ≤ |y 1| * q :=
    (stableRescaledFlow_wall_decay hc hm.le hu.le hw.le hs).1.trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) (abs_nonneg _))
  obtain ⟨hm', hu', hw'⟩ := stableRescaledFlow_band hc hm.le hu.le hw.le hs
  have hlin := (stableRescaledJacobian_strong_offDiagonal (v := H) hc hm' hu' hw').trans
    (mul_le_mul (mul_le_mul_of_nonneg_left hU (by norm_num : (0 : ℝ) ≤ 96))
      (stableRescaledSecondDifferential_bound hc hm hu hw hs v w) (norm_nonneg _) (by positivity))
  have hbudget := mul_le_mul_of_nonneg_left hB0 (show 0 ≤ 3840000 * E ^ 3 * q by positivity)
  have hforce := stableSecondStrongForcing_decay hc hm.le hu.le hw.le hs v w
  have hE23 : E ^ 2 ≤ E ^ 3 := by nlinarith [sq_nonneg E]
  have hforce' := mul_le_mul_of_nonneg_right hE23 (mul_nonneg hB hq)
  have Hsum := abs_add_le
    ((c + 1) * stableOriginalJacobian Y 1 0 * H 0 + (c + 1) * stableOriginalJacobian Y 1 2 * H 2)
    (((c + 1) • stableOriginalHessian Y
      (stableRescaledDifferential (c + 1) y s v) (stableRescaledDifferential (c + 1) y s w)) 1)
  change _ ≤ 15000000 * E ^ 3 * B * q
  nlinarith only [Hsum, hlin, hbudget, hforce, hforce', mul_nonneg (pow_nonneg (by linarith : 0 ≤ E) 3) (mul_nonneg hB hq)]

end BianchiIX
