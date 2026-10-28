import BianchiIX.Dynamics.StableClockTailDerivatives

noncomputable section

namespace BianchiIX

open Set Filter MeasureTheory
open scoped Topology

theorem stableProjectiveCutoff_tendsto {c : ℝ} {y : StableState}
    (hc : 2 ≤ c) (hy : y ∈ stableParameterDomain c) :
    Tendsto (fun s => stableProjectiveCutoff c (y, s)) atTop atTop := by
  refine tendsto_atTop_mono' atTop ?_
    (Tendsto.const_mul_atTop (by linarith : 0 < (c + 1) / 18) tendsto_id)
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with s hs
  calc
    (c + 1) / 18 * id s = (c + 1) * s / 18 := by dsimp; ring
    _ ≤ stableProjectiveCutoff c (y, s) := (stableProjectiveCutoff_bounds hc hy hs).1

theorem stableClockFlow_limit {c : ℝ} {y : StableState}
    (hc : 2 ≤ c) (hy : y ∈ stableParameterDomain c) :
    Tendsto (fun s => stableClockFlow c (y, s)) atTop
      (𝓝 ![stableBoundaryProjection (y 0) (y 1) (y 2), 0, 0]) := by
  have H := (stableOriginalFlow_limit hc hy.1.le hy.2.1.le hy.2.2.le).comp
    (stableProjectiveCutoff_tendsto hc hy)
  apply H.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with s hs
  exact (stableClockFlow_eq_original hc hy hs).symm

theorem stableClockTailIntegral_eq_projectiveTail {c T : ℝ} {y : StableState}
    (hc : 2 ≤ c) (hy : y ∈ stableParameterDomain c) (hT : 0 ≤ T) :
    stableClockTailIntegral c T y = stableProjectiveTail c T y := by
  obtain ⟨C, hC, HC⟩ := exists_stableClockResidual_derivative_integral_tails
  have hint := (HC c T y hc hy hT).1.1
  have hP : 1 < stableBoundaryProjection (y 0) (y 1) (y 2) := by
    have H := (abs_le.mp (stableBoundaryProjection_band hc hy.1.le hy.2.1.le hy.2.2.le)).1
    linarith
  have hlim := (contDiffAt_stableCorrectedPhase 2
    (y := ![stableBoundaryProjection (y 0) (y 1) (y 2), 0, 0]) hP).continuousAt.tendsto.comp
      (stableClockFlow_limit hc hy)
  change Tendsto (fun s => stableCorrectedPhase (stableClockFlow c (y, s) 0)
    (stableClockFlow c (y, s) 1) (stableClockFlow c (y, s) 2)) atTop
    (𝓝 (stableCorrectedPhase (stableBoundaryProjection (y 0) (y 1) (y 2)) 0 0)) at hlim
  rw [stableCorrectedPhase_zero (by linarith)] at hlim
  rw [stableProjectiveTail_eq_clockFlow hc hy hT]
  exact integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun s hs => hasDerivAt_stableClock_correctedPhase hc hy (le_trans hT hs)) hint hlim

theorem stableClockTailIntegral_eventually_eq {c T : ℝ} {y : StableState}
    (hc : 2 ≤ c) (hy : y ∈ stableParameterDomain c) (hT : 0 ≤ T) :
    stableClockTailIntegral c T =ᶠ[𝓝 y] stableProjectiveTail c T := by
  filter_upwards [(isOpen_stableParameterDomain c).mem_nhds hy] with z hz
  exact stableClockTailIntegral_eq_projectiveTail hc hz hT

theorem stableProjectiveTail_fderiv_clockIntegral {c T : ℝ} {y : StableState}
    (hc : 2 ≤ c) (hy : y ∈ stableParameterDomain c) (hT : 0 ≤ T) (v : StableState) :
    fderiv ℝ (stableProjectiveTail c T) y v =
      ∫ s in Ioi T, fderiv ℝ (stableClockResidualRate c s) y v := by
  rw [← (stableClockTailIntegral_eventually_eq hc hy hT).fderiv_eq]
  exact stableClockTailIntegral_fderiv_apply hc hy hT v

theorem stableProjectiveTail_fderiv2_clockIntegral {c T : ℝ} {y : StableState}
    (hc : 2 ≤ c) (hy : y ∈ stableParameterDomain c) (hT : 0 ≤ T) (v w : StableState) :
    fderiv ℝ (fderiv ℝ (stableProjectiveTail c T)) y v w =
      ∫ s in Ioi T, fderiv ℝ (fderiv ℝ (stableClockResidualRate c s)) y v w := by
  rw [← (stableClockTailIntegral_eventually_eq hc hy hT).fderiv.fderiv_eq]
  exact stableClockTailIntegral_fderiv2_apply hc hy hT v w

end BianchiIX
