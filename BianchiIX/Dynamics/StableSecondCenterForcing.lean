import BianchiIX.Dynamics.StableCenterHessianBounds
import BianchiIX.Dynamics.StableCenterInputGrowth

noncomputable section

namespace BianchiIX

theorem stableSecondCenterForcing_of_stableBounds {y v w : StableState} {c s N M : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 40)
    (hu : |y 1| ≤ 1 / 200) (hw : |y 2| ≤ 1 / 200) (hs : 0 ≤ s)
    (hN : 0 ≤ N) (hM : 0 ≤ M)
    (hvz : ‖![stableRescaledDifferential (c + 1) y s v 1,
      stableRescaledDifferential (c + 1) y s v 2]‖ ≤ N * Real.exp (-s / 4))
    (hwz : ‖![stableRescaledDifferential (c + 1) y s w 1,
      stableRescaledDifferential (c + 1) y s w 2]‖ ≤ M * Real.exp (-s / 4)) :
    |((c + 1) • stableOriginalHessian (stableRescaledFlow (c + 1) y s)
      (stableRescaledDifferential (c + 1) y s v) (stableRescaledDifferential (c + 1) y s w)) 0| ≤
      1024 * ((|y 1| + |y 2|) ^ 2 * (Real.exp (512 * (|y 1| + |y 2|)) * ‖v‖) *
          (Real.exp (512 * (|y 1| + |y 2|)) * ‖w‖) +
        (|y 1| + |y 2|) * ((Real.exp (512 * (|y 1| + |y 2|)) * ‖v‖) * M +
          N * (Real.exp (512 * (|y 1| + |y 2|)) * ‖w‖)) + N * M) * Real.exp (-s / 4) := by
  have hb : 0 ≤ |y 1| + |y 2| := by positivity
  have hy := (stableRescaledFlow_amplitude_decay hc hm hu hw hs).trans
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith : -s / 2 ≤ -s / 4)) hb)
  have H := stableCenterHessianBudget_transport hb (by positivity) (by positivity) hN hM
    (Real.exp_pos _).le (Real.exp_le_one_iff.mpr (by linarith : -s / 4 ≤ 0)) hy
    (stableRescaledDifferential_bound hc hm hu hw hs v)
    (stableRescaledDifferential_bound hc hm hu hw hs w) hvz hwz
  obtain ⟨hm', hu', hw'⟩ := stableRescaledFlow_band hc hm hu hw hs
  exact (stableRescaledHessian_center_bound hc hm' hu' hw' _ _).trans
    (by convert! mul_le_mul_of_nonneg_left H (by norm_num : (0 : ℝ) ≤ 1024) using 1; ring)

theorem stableSecondCenterForcing_centerInputs {y v w : StableState} {c s : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 40)
    (hu : |y 1| ≤ 1 / 200) (hw : |y 2| ≤ 1 / 200) (hs : 0 ≤ s)
    (hv1 : v 1 = 0) (hv2 : v 2 = 0) (hw1 : w 1 = 0) (hw2 : w 2 = 0) :
    |((c + 1) • stableOriginalHessian (stableRescaledFlow (c + 1) y s)
      (stableRescaledDifferential (c + 1) y s v) (stableRescaledDifferential (c + 1) y s w)) 0| ≤
      70000000 * (|y 1| + |y 2|) ^ 2 * Real.exp (512 * (|y 1| + |y 2|)) ^ 2 *
        ‖v‖ * ‖w‖ * Real.exp (-s / 4) := by
  have H := stableSecondCenterForcing_of_stableBounds hc hm hu hw hs (by positivity) (by positivity)
    (stableRescaledDifferential_stable_centerInput hc hm hu hw hs hv1 hv2)
    (stableRescaledDifferential_stable_centerInput hc hm hu hw hs hw1 hw2)
  have hn : 0 ≤ (|y 1| + |y 2|) ^ 2 * Real.exp (512 * (|y 1| + |y 2|)) ^ 2 *
      ‖v‖ * ‖w‖ * Real.exp (-s / 4) := by positivity
  nlinarith only [H, hn]

theorem stableSecondCenterForcing_centerInput {y v w : StableState} {c s : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 40)
    (hu : |y 1| ≤ 1 / 200) (hw : |y 2| ≤ 1 / 200) (hs : 0 ≤ s)
    (hv1 : v 1 = 0) (hv2 : v 2 = 0) :
    |((c + 1) • stableOriginalHessian (stableRescaledFlow (c + 1) y s)
      (stableRescaledDifferential (c + 1) y s v) (stableRescaledDifferential (c + 1) y s w)) 0| ≤
      2000000 * (|y 1| + |y 2|) * Real.exp (512 * (|y 1| + |y 2|)) ^ 2 *
        ‖v‖ * ‖w‖ * Real.exp (-s / 4) := by
  let b := |y 1| + |y 2|
  let E := Real.exp (512 * b)
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hb1 : b ≤ 1 := by dsimp [b]; linarith
  have H := stableSecondCenterForcing_of_stableBounds hc hm hu hw hs (by positivity) (by positivity)
    (stableRescaledDifferential_stable_centerInput hc hm hu hw hs hv1 hv2)
    (stableRescaledDifferential_stable_uniform_decay hc hm hu hw hs w)
  have H2 := mul_le_mul_of_nonneg_right (show b ^ 2 ≤ b by nlinarith)
    (show 0 ≤ E ^ 2 * ‖v‖ * ‖w‖ * Real.exp (-s / 4) by positivity)
  have hn : 0 ≤ b * E ^ 2 * ‖v‖ * ‖w‖ * Real.exp (-s / 4) := by positivity
  change _ ≤ 2000000 * b * E ^ 2 * ‖v‖ * ‖w‖ * Real.exp (-s / 4)
  nlinarith only [H, H2, hn]

end BianchiIX
