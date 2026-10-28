import BianchiIX.Dynamics.StableClockResidualFactor
import BianchiIX.Dynamics.StableResidualProduct

noncomputable section

namespace BianchiIX

theorem exists_stableClockResidualState_bounds :
    ∃ C > (0 : ℝ), ∀ (c : ℝ) (y : StableState), 2 ≤ c → |y 0 - c| ≤ 1 / 10 →
      |y 1| ≤ 1 / 100 → |y 2| ≤ 1 / 100 →
      ContDiffAt ℝ 2 (stableClockResidualState c) y ∧
        |stableClockResidualState c y| ≤ C / (c + 1) ^ 2 * |y 1| * (|y 1| + |y 2|) ^ 3 ∧
        (∀ v, |fderiv ℝ (stableClockResidualState c) y v| ≤
          C / (c + 1) ^ 2 * (|v 1| * (|y 1| + |y 2|) ^ 3 + |y 1| * stableCubicFirstBudget y v)) ∧
        (∀ v w, |fderiv ℝ (fderiv ℝ (stableClockResidualState c)) y v w| ≤
          C / (c + 1) ^ 2 * (|v 1| * stableCubicFirstBudget y w + |w 1| * stableCubicFirstBudget y v +
            |y 1| * stableCubicSecondBudget y v w)) := by
  obtain ⟨C, hC, HC⟩ := exists_stableScaledResidual_derivative_bounds
  refine ⟨4 * C, by positivity, ?_⟩
  intro c y hc hm hu hw
  obtain ⟨hg, hg0, hg1, hg2⟩ := HC c y hc hm hu hw
  obtain ⟨hf0, hf1, hf2⟩ := stableClockResidualFactor_bounds hc hm hu hw
  have hf := (contDiff_stableClockResidualFactor c 2).contDiffAt (x := y)
  have H := stableResidual_product_bounds (by positivity : 0 ≤ C / (c + 1) ^ 2)
    hf hg hf0 hf1 hf2 hg0 hg1 hg2
  have he : stableClockResidualState c =
      fun z => stableClockResidualFactor c z * stableScaledResidual (c + 1) z :=
    funext (stableClockResidualState_factor hc)
  rw [he]
  refine ⟨hf.mul hg, ?_⟩
  have hscale : 4 * (C / (c + 1) ^ 2) = 4 * C / (c + 1) ^ 2 := by ring
  simpa only [hscale] using H

end BianchiIX
