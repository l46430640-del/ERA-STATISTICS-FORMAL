import BianchiIX.Dynamics.StableClockFlow
import BianchiIX.Dynamics.StableProjectiveTail

noncomputable section

namespace BianchiIX

open Set Filter MeasureTheory
open scoped Topology

def stableClockResidual (c : ℝ) (p : StableState × ℝ) : ℝ :=
  let Y := stableClockFlow c p
  stableCorrectedResidual (Y 0) (Y 1) (Y 2) / (c + 1)

theorem stableClockFlow_center_gt_one {c σ : ℝ} {y : StableState}
    (hc : 2 ≤ c) (hy : y ∈ stableParameterDomain c) (hσ : 0 ≤ σ) :
    1 < stableClockFlow c (y, σ) 0 := by
  have H := (abs_le.mp (stableClockFlow_band hc hy hσ).1).1
  linarith

theorem contDiffAt_stableClockResidual_two {c σ : ℝ} {y : StableState}
    (hc : 2 ≤ c) (hy : y ∈ stableParameterDomain c) (hσ : 0 ≤ σ) :
    ContDiffAt ℝ 2 (stableClockResidual c) (y, σ) := by
  have H := (contDiffAt_stableCorrectedResidual 2 (stableClockFlow_center_gt_one hc hy hσ)).comp
    (y, σ) (g := fun z : StableState => stableCorrectedResidual (z 0) (z 1) (z 2))
    (f := stableClockFlow c) (contDiffAt_stableClockFlow_two hc hy hσ)
  exact H.div_const _

theorem hasDerivAt_stableClock_correctedPhase {c σ : ℝ} {y : StableState}
    (hc : 2 ≤ c) (hy : y ∈ stableParameterDomain c) (hσ : 0 ≤ σ) :
    HasDerivAt (fun s => stableCorrectedPhase (stableClockFlow c (y, s) 0)
      (stableClockFlow c (y, s) 1) (stableClockFlow c (y, s) 2))
      (stableClockResidual c (y, σ)) σ := by
  have hY := stableInclusion.hasFDerivAt.comp_hasDerivAt σ (hasDerivAt_stableClockFlow_time hc hy hσ)
  rw [stableClockField, map_smul, ← stableBoundaryField_inclusion] at hY
  have H := hasDerivAt_stableCorrectedPhase_scaled hY (stableClockFlow_center_gt_one hc hy hσ) (by rfl)
  convert! H using 1
  simp [stableClockResidual, stableInclusion_apply, div_eq_mul_inv, mul_comm]

theorem stableClockResidual_integral {c σ : ℝ} {y : StableState}
    (hc : 2 ≤ c) (hy : y ∈ stableParameterDomain c) (hσ : 0 ≤ σ) :
    (∫ s in 0..σ, stableClockResidual c (y, s)) =
      stableCorrectedPhase (stableClockFlow c (y, σ) 0)
        (stableClockFlow c (y, σ) 1) (stableClockFlow c (y, σ) 2) -
      stableCorrectedPhase (y 0) (y 1) (y 2) := by
  have hcont : ContinuousOn (fun s => stableClockResidual c (y, s)) (Icc 0 σ) :=
    fun s hs => ((contDiffAt_stableClockResidual_two hc hy hs.1).continuousAt.comp
      (continuousAt_const.prodMk continuousAt_id)).continuousWithinAt
  have H := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s hs => hasDerivAt_stableClock_correctedPhase hc hy (show 0 ≤ s from (uIcc_of_le hσ ▸ hs).1))
    (hcont.intervalIntegrable_of_Icc hσ)
  simpa only [stableClockFlow_initial hc] using H

theorem stableProjectiveTail_eq_clockFlow {c σ : ℝ} {y : StableState}
    (hc : 2 ≤ c) (hy : y ∈ stableParameterDomain c) (hσ : 0 ≤ σ) :
    stableProjectiveTail c σ y = stableBoundaryProjection (y 0) (y 1) (y 2) -
      stableCorrectedPhase (stableClockFlow c (y, σ) 0)
        (stableClockFlow c (y, σ) 1) (stableClockFlow c (y, σ) 2) := by
  rw [stableProjectiveTail_eq_original hc, stableClockFlow_eq_original hc hy hσ]
  simp [stableCorrectedApproximation, stableOriginalFlow_eq, stableRestriction_apply]

theorem stableProjectiveTail_eq_clockIntegral {c σ : ℝ} {y : StableState}
    (hc : 2 ≤ c) (hy : y ∈ stableParameterDomain c) (hσ : 0 ≤ σ) :
    stableProjectiveTail c σ y = stableCorrectedRemainder y -
      ∫ s in 0..σ, stableClockResidual c (y, s) := by
  rw [stableProjectiveTail_eq_clockFlow hc hy hσ, stableClockResidual_integral hc hy hσ]
  unfold stableCorrectedRemainder
  ring

end BianchiIX
