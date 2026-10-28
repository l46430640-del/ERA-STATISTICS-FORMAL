import BianchiIX.Dynamics.StableHessianBounds
import BianchiIX.Dynamics.StableSecondVariation

noncomputable section

namespace BianchiIX

theorem stableRescaledDifferential_stable_uniform_decay {y : StableState} {c s : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 40)
    (hu : |y 1| ≤ 1 / 200) (hw : |y 2| ≤ 1 / 200) (hs : 0 ≤ s) (v : StableState) :
    ‖![stableRescaledDifferential (c + 1) y s v 1, stableRescaledDifferential (c + 1) y s v 2]‖ ≤
      4 * Real.exp (512 * (|y 1| + |y 2|)) * ‖v‖ * Real.exp (-s / 4) := by
  let b := |y 1| + |y 2|
  let E := Real.exp (512 * b)
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hb1 : b ≤ 1 / 100 := by dsimp [b]; linarith
  have hE : 1 ≤ E := Real.one_le_exp (by positivity)
  have hcoef : ‖![v 1, v 2]‖ + 256 * b * E * ‖v‖ ≤ 4 * E * ‖v‖ := by
    have H := mul_le_mul_of_nonneg_right ((stableTangent_split_bounds v).2.2)
      (show 0 ≤ (1 : ℝ) by norm_num)
    have H1 := mul_le_mul_of_nonneg_right hE (norm_nonneg v)
    have H2 := mul_le_mul_of_nonneg_right hb1 (show 0 ≤ E * ‖v‖ by positivity)
    nlinarith only [H, H1, H2, norm_nonneg v]
  exact (stableRescaledDifferential_stable_decay hc hm hu hw hs v).trans
    (mul_le_mul_of_nonneg_right hcoef (Real.exp_pos _).le)

theorem stableHessianBudget_along_variations {y : StableState} {c s : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 40)
    (hu : |y 1| ≤ 1 / 200) (hw : |y 2| ≤ 1 / 200) (hs : 0 ≤ s) (v w : StableState) :
    stableHessianBudget (stableRescaledFlow (c + 1) y s)
      (stableRescaledDifferential (c + 1) y s v) (stableRescaledDifferential (c + 1) y s w) ≤
        9 * Real.exp (512 * (|y 1| + |y 2|)) ^ 2 * ‖v‖ * ‖w‖ * Real.exp (-s / 4) := by
  let E := Real.exp (512 * (|y 1| + |y 2|))
  let Jv := stableRescaledDifferential (c + 1) y s v
  let Jw := stableRescaledDifferential (c + 1) y s w
  let Y := stableRescaledFlow (c + 1) y s
  have hJv := stableRescaledDifferential_bound hc hm hu hw hs v
  have hJw := stableRescaledDifferential_bound hc hm hu hw hs w
  have hZv := stableRescaledDifferential_stable_uniform_decay hc hm hu hw hs v
  have hZw := stableRescaledDifferential_stable_uniform_decay hc hm hu hw hs w
  have hb : |Y 1| + |Y 2| ≤ Real.exp (-s / 4) := by
    have H := stableRescaledFlow_amplitude_decay hc hm hu hw hs
    have Hb : |y 1| + |y 2| ≤ 1 := by linarith
    have He : Real.exp (-s / 2) ≤ Real.exp (-s / 4) := Real.exp_le_exp.mpr (by linarith)
    exact H.trans ((mul_le_mul_of_nonneg_right Hb (Real.exp_pos _).le).trans (by simpa using He))
  have H0 := mul_le_mul (mul_le_mul hb hJv (norm_nonneg _) (Real.exp_pos _).le)
    hJw (norm_nonneg _) (by positivity)
  have H1 := mul_le_mul hZv hJw (norm_nonneg _) (by positivity)
  have H2 := mul_le_mul hJv hZw (norm_nonneg _) (by positivity)
  change (|Y 1| + |Y 2|) * ‖Jv‖ * ‖Jw‖ + ‖![Jv 1, Jv 2]‖ * ‖Jw‖ +
    ‖Jv‖ * ‖![Jw 1, Jw 2]‖ ≤ _
  nlinarith only [H0, H1, H2]

theorem stableSecondForcing_decay {y : StableState} {c s : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 40)
    (hu : |y 1| ≤ 1 / 200) (hw : |y 2| ≤ 1 / 200) (hs : 0 ≤ s) (v w : StableState) :
    ‖(c + 1) • stableOriginalHessian (stableRescaledFlow (c + 1) y s)
      (stableRescaledDifferential (c + 1) y s v) (stableRescaledDifferential (c + 1) y s w)‖ ≤
        10000 * Real.exp (512 * (|y 1| + |y 2|)) ^ 2 * ‖v‖ * ‖w‖ * Real.exp (-s / 4) := by
  obtain ⟨hm', hu', hw'⟩ := stableRescaledFlow_band hc hm hu hw hs
  have H := (stableRescaledHessian_bound hc hm' hu' hw'
    (stableRescaledDifferential (c + 1) y s v) (stableRescaledDifferential (c + 1) y s w)).trans
      (mul_le_mul_of_nonneg_left (stableHessianBudget_along_variations hc hm hu hw hs v w)
        (by norm_num : (0 : ℝ) ≤ 1024))
  have hnonneg : 0 ≤ Real.exp (512 * (|y 1| + |y 2|)) ^ 2 * ‖v‖ * ‖w‖ * Real.exp (-s / 4) := by positivity
  nlinarith only [H, hnonneg]

end BianchiIX
