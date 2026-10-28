import BianchiIX.Dynamics.StableSecondStrongDecay

noncomputable section

namespace BianchiIX

theorem stableStrongHessianBudget_bound (y v w : StableState) :
    stableStrongHessianBudget y v w ≤ (2 + 3 * (|y 1| + |y 2|)) * ‖v‖ * ‖w‖ := by
  have hv (i : Fin 3) : |v i| ≤ ‖v‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm v i
  have hw (i : Fin 3) : |w i| ≤ ‖w‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm w i
  have HT : |v 0| * |w 1| + |v 1| * |w 0| ≤ 2 * ‖v‖ * ‖w‖ := by
    nlinarith only [mul_le_mul (hv 0) (hw 1) (abs_nonneg _) (norm_nonneg _),
      mul_le_mul (hv 1) (hw 0) (abs_nonneg _) (norm_nonneg _)]
  have HS : |v 1| * ‖w‖ + ‖v‖ * |w 1| ≤ 2 * ‖v‖ * ‖w‖ := by
    nlinarith only [mul_le_mul_of_nonneg_right (hv 1) (norm_nonneg w),
      mul_le_mul_of_nonneg_left (hw 1) (norm_nonneg v)]
  have H := mul_le_mul_of_nonneg_left HS (show 0 ≤ |y 1| + |y 2| by positivity)
  unfold stableStrongHessianBudget
  nlinarith only [HT, H, mul_nonneg (abs_nonneg (y 2)) (mul_nonneg (norm_nonneg v) (norm_nonneg w))]

theorem stableStrongHessianBudget_stable {y v w : StableState} (hv : v 0 = 0) (hw : w 0 = 0) :
    stableStrongHessianBudget y v w ≤ 3 * (|y 1| + |y 2|) * ‖v‖ * ‖w‖ := by
  have Hv : |v 1| ≤ ‖v‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm v 1
  have Hw : |w 1| ≤ ‖w‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm w 1
  have HS : |v 1| * ‖w‖ + ‖v‖ * |w 1| ≤ 2 * ‖v‖ * ‖w‖ := by
    nlinarith only [mul_le_mul_of_nonneg_right Hv (norm_nonneg w),
      mul_le_mul_of_nonneg_left Hw (norm_nonneg v)]
  have H := mul_le_mul_of_nonneg_left HS (show 0 ≤ |y 1| + |y 2| by positivity)
  simp only [stableStrongHessianBudget, hv, hw, abs_zero, zero_mul, mul_zero, add_zero]
  nlinarith only [H, mul_nonneg (abs_nonneg (y 2)) (mul_nonneg (norm_nonneg v) (norm_nonneg w))]

theorem stableStrongHessianBudget_noStrong {y v w : StableState} (hv : v 1 = 0) (hw : w 1 = 0) :
    stableStrongHessianBudget y v w = |y 1| * ‖v‖ * ‖w‖ := by
  simp [stableStrongHessianBudget, hv, hw]

theorem stableRescaledSecondDifferential_strong_uniform {y : StableState} {c s : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| < 1 / 40)
    (hu : |y 1| < 1 / 200) (hw : |y 2| < 1 / 200) (hs : 0 ≤ s) (v w : StableState) :
    |stableRescaledSecondDifferential (c + 1) y s v w 1| ≤
      (480000000 * Real.exp (512 * (|y 1| + |y 2|)) ^ 3 * ‖v‖ * ‖w‖ / (c + 1)) *
        Real.exp (-3 * (c + 1) / 32 * s) := by
  have hK : 0 < c + 1 := by linarith
  have hB : stableStrongHessianBudget y v w ≤ 3 * ‖v‖ * ‖w‖ :=
    (stableStrongHessianBudget_bound y v w).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (show 2 + 3 * (|y 1| + |y 2|) ≤ 3 by linarith) (norm_nonneg v)) (norm_nonneg w))
  have H := mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hB
      (show 0 ≤ 160000000 * Real.exp (512 * (|y 1| + |y 2|)) ^ 3 by positivity)) hK.le)
    (Real.exp_pos (-3 * (c + 1) / 32 * s)).le
  exact (stableRescaledSecondDifferential_strong_decay hc hm hu hw hs v w).trans (by convert! H using 1; ring)

theorem stableRescaledSecondDifferential_strong_stableInputs {y v w : StableState} {c s : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| < 1 / 40)
    (hu : |y 1| < 1 / 200) (hw : |y 2| < 1 / 200) (hs : 0 ≤ s)
    (hv : v 0 = 0) (hw0 : w 0 = 0) :
    |stableRescaledSecondDifferential (c + 1) y s v w 1| ≤
      (480000000 * (|y 1| + |y 2|) * Real.exp (512 * (|y 1| + |y 2|)) ^ 3 * ‖v‖ * ‖w‖ / (c + 1)) *
        Real.exp (-3 * (c + 1) / 32 * s) := by
  have hK : 0 < c + 1 := by linarith
  have H := mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (stableStrongHessianBudget_stable (y := y) hv hw0)
      (show 0 ≤ 160000000 * Real.exp (512 * (|y 1| + |y 2|)) ^ 3 by positivity)) hK.le)
    (Real.exp_pos (-3 * (c + 1) / 32 * s)).le
  exact (stableRescaledSecondDifferential_strong_decay hc hm hu hw hs v w).trans (by convert! H using 1; ring)

theorem stableRescaledSecondDifferential_strong_noStrongInputs {y v w : StableState} {c s : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| < 1 / 40)
    (hu : |y 1| < 1 / 200) (hw : |y 2| < 1 / 200) (hs : 0 ≤ s)
    (hv : v 1 = 0) (hw1 : w 1 = 0) :
    |stableRescaledSecondDifferential (c + 1) y s v w 1| ≤
      (160000000 * |y 1| * Real.exp (512 * (|y 1| + |y 2|)) ^ 3 * ‖v‖ * ‖w‖ / (c + 1)) *
        Real.exp (-3 * (c + 1) / 32 * s) := by
  have H := stableRescaledSecondDifferential_strong_decay hc hm hu hw hs v w
  rw [stableStrongHessianBudget_noStrong hv hw1] at H
  convert! H using 1
  ring

end BianchiIX
