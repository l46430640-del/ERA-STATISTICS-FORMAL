import BianchiIX.Dynamics.StableSecondForcing

noncomputable section

namespace BianchiIX

theorem stableRescaledDifferential_stable_centerInput {y v : StableState} {c s : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 40)
    (hu : |y 1| ≤ 1 / 200) (hw : |y 2| ≤ 1 / 200) (hs : 0 ≤ s)
    (hv1 : v 1 = 0) (hv2 : v 2 = 0) :
    ‖![stableRescaledDifferential (c + 1) y s v 1, stableRescaledDifferential (c + 1) y s v 2]‖ ≤
      256 * (|y 1| + |y 2|) * Real.exp (512 * (|y 1| + |y 2|)) * ‖v‖ * Real.exp (-s / 4) := by
  have hz : (![v 1, v 2] : Fin 2 → ℝ) = 0 := by ext i; fin_cases i <;> simp [hv1, hv2]
  simpa only [hz, norm_zero, zero_add] using
    stableRescaledDifferential_stable_decay hc hm hu hw hs v

theorem stableSecondForcing_centerInputs {y v w : StableState} {c s : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 40)
    (hu : |y 1| ≤ 1 / 200) (hw : |y 2| ≤ 1 / 200) (hs : 0 ≤ s)
    (hv1 : v 1 = 0) (hv2 : v 2 = 0) (hw1 : w 1 = 0) (hw2 : w 2 = 0) :
    ‖(c + 1) • stableOriginalHessian (stableRescaledFlow (c + 1) y s)
        (stableRescaledDifferential (c + 1) y s v) (stableRescaledDifferential (c + 1) y s w)‖ ≤
      600000 * (|y 1| + |y 2|) * Real.exp (512 * (|y 1| + |y 2|)) ^ 2 * ‖v‖ * ‖w‖ * Real.exp (-s / 4) := by
  let b := |y 1| + |y 2|
  let E := Real.exp (512 * b)
  let Jv := stableRescaledDifferential (c + 1) y s v
  let Jw := stableRescaledDifferential (c + 1) y s w
  let Y := stableRescaledFlow (c + 1) y s
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hJv := stableRescaledDifferential_bound hc hm hu hw hs v
  have hJw := stableRescaledDifferential_bound hc hm hu hw hs w
  have hZv := stableRescaledDifferential_stable_centerInput hc hm hu hw hs hv1 hv2
  have hZw := stableRescaledDifferential_stable_centerInput hc hm hu hw hs hw1 hw2
  have hbdec : |Y 1| + |Y 2| ≤ b * Real.exp (-s / 4) :=
    (stableRescaledFlow_amplitude_decay hc hm hu hw hs).trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith : -s / 2 ≤ -s / 4)) hb)
  have H0 := mul_le_mul (mul_le_mul hbdec hJv (norm_nonneg _) (by positivity))
    hJw (norm_nonneg _) (by positivity)
  have H1 := mul_le_mul hZv hJw (norm_nonneg _) (by positivity)
  have H2 := mul_le_mul hJv hZw (norm_nonneg _) (by positivity)
  obtain ⟨hm', hu', hw'⟩ := stableRescaledFlow_band hc hm hu hw hs
  have H := stableRescaledHessian_bound hc hm' hu' hw' Jv Jw
  dsimp only [stableHessianBudget] at H
  change ‖(c + 1) • stableOriginalHessian Y Jv Jw‖ ≤
    600000 * b * E ^ 2 * ‖v‖ * ‖w‖ * Real.exp (-s / 4)
  have hn : 0 ≤ b * E ^ 2 * ‖v‖ * ‖w‖ * Real.exp (-s / 4) := by positivity
  nlinarith only [H, H0, H1, H2, hn]

end BianchiIX
