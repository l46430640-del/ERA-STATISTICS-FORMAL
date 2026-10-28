import BianchiIX.Dynamics.StableResidualTailDerivatives
import BianchiIX.Dynamics.StableProjectionSecondRegularity

noncomputable section

namespace BianchiIX

open Set Filter MeasureTheory
open scoped Topology

def stableCorrectedRemainder (y : StableState) : ℝ :=
  stableBoundaryProjection (y 0) (y 1) (y 2) - stableCorrectedPhase (y 0) (y 1) (y 2)

def stableCorrectedPhaseTail (K T : ℝ) (y : StableState) : ℝ :=
  stableBoundaryProjection (y 0) (y 1) (y 2) -
    stableCorrectedPhase (stableRescaledFlow K y T 0) (stableRescaledFlow K y T 1) (stableRescaledFlow K y T 2)

theorem stableCorrectedPhaseTail_zero (K : ℝ) : stableCorrectedPhaseTail K 0 = stableCorrectedRemainder := by
  funext y
  simp only [stableCorrectedPhaseTail, stableRescaledFlow_initial, stableCorrectedRemainder]

theorem stableResidualTailIntegral_eq_correctedPhaseTail {c T : ℝ} {y : StableState}
    (hc : 2 ≤ c) (hy : y ∈ stableParameterDomain c) (hT : 0 ≤ T) :
    stableResidualTailIntegral (c + 1) T y = stableCorrectedPhaseTail (c + 1) T y := by
  have hK : 0 < c + 1 := by linarith
  obtain ⟨C, hC, HC⟩ := exists_stableResidual_derivative_integral_tails
  have hint := (HC c T y hc hy.1 hy.2.1 hy.2.2 hT).1.1
  have hP : 1 < stableBoundaryProjection (y 0) (y 1) (y 2) := by
    have H := (abs_le.mp (stableBoundaryProjection_band hc hy.1.le hy.2.1.le hy.2.2.le)).1
    linarith
  have hlim := (contDiffAt_stableCorrectedPhase 2
    (y := ![stableBoundaryProjection (y 0) (y 1) (y 2), 0, 0]) hP).continuousAt.tendsto.comp
      (stableRescaledFlow_limit hK hc hy.1.le hy.2.1.le hy.2.2.le)
  change Tendsto (fun s => stableCorrectedPhase (stableRescaledFlow (c + 1) y s 0)
    (stableRescaledFlow (c + 1) y s 1) (stableRescaledFlow (c + 1) y s 2)) atTop
    (𝓝 (stableCorrectedPhase (stableBoundaryProjection (y 0) (y 1) (y 2)) 0 0)) at hlim
  rw [stableCorrectedPhase_zero (by linarith)] at hlim
  exact integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun s hs => hasDerivAt_stableCorrectedPhase_rescaled hc hy.1.le hy.2.1.le hy.2.2.le (le_trans hT hs))
    hint hlim

theorem contDiffAt_stableCorrectedPhaseTail_two {c T : ℝ} {y : StableState}
    (hc : 2 ≤ c) (hy : y ∈ stableParameterDomain c) (hT : 0 ≤ T) :
    ContDiffAt ℝ 2 (stableCorrectedPhaseTail (c + 1) T) y := by
  have hK : 0 < c + 1 := by linarith
  have hp : ContDiffAt ℝ 2 (fun z : StableState => (z, T)) y := contDiffAt_id.prodMk contDiffAt_const
  have hflow := (contDiffAt_stableRescaledFlow_two hK hc hy.1.le hy.2.1.le hy.2.2.le hT).comp y hp
  have hM : 1 < stableRescaledFlow (c + 1) y T 0 := by
    have H := (abs_le.mp (stableRescaledFlow_band hc hy.1.le hy.2.1.le hy.2.2.le hT).1).1
    linarith
  have hphase := (contDiffAt_stableCorrectedPhase 2 (y := stableRescaledFlow (c + 1) y T) hM).comp y hflow
  exact (contDiffAt_stableBoundaryProjection_two_in_band hc hy.1 hy.2.1 hy.2.2).sub hphase

theorem stableResidualTailIntegral_eventually_eq {c T : ℝ} {y : StableState}
    (hc : 2 ≤ c) (hy : y ∈ stableParameterDomain c) (hT : 0 ≤ T) :
    stableResidualTailIntegral (c + 1) T =ᶠ[𝓝 y] stableCorrectedPhaseTail (c + 1) T := by
  filter_upwards [(isOpen_stableParameterDomain c).mem_nhds hy] with z hz
  exact stableResidualTailIntegral_eq_correctedPhaseTail hc hz hT

theorem stableCorrectedPhaseTail_fderiv_apply {c T : ℝ} {y : StableState}
    (hc : 2 ≤ c) (hy : y ∈ stableParameterDomain c) (hT : 0 ≤ T) (v : StableState) :
    fderiv ℝ (stableCorrectedPhaseTail (c + 1) T) y v =
      ∫ s in Ioi T, fderiv ℝ (stableRescaledResidualRate (c + 1) s) y v := by
  rw [← (stableResidualTailIntegral_eventually_eq hc hy hT).fderiv_eq]
  exact stableResidualTailIntegral_fderiv_apply hc hy hT v

theorem stableCorrectedPhaseTail_fderiv2_apply {c T : ℝ} {y : StableState}
    (hc : 2 ≤ c) (hy : y ∈ stableParameterDomain c) (hT : 0 ≤ T) (v w : StableState) :
    fderiv ℝ (fderiv ℝ (stableCorrectedPhaseTail (c + 1) T)) y v w =
      ∫ s in Ioi T, fderiv ℝ (fderiv ℝ (stableRescaledResidualRate (c + 1) s)) y v w := by
  rw [← (stableResidualTailIntegral_eventually_eq hc hy hT).fderiv.fderiv_eq]
  exact stableResidualTailIntegral_fderiv2_apply hc hy hT v w

theorem stableCorrectedPhaseTail_eq_remainder_sub_integral {c T : ℝ} {y : StableState}
    (hc : 2 ≤ c) (hy : y ∈ stableParameterDomain c) (hT : 0 ≤ T) :
    stableCorrectedPhaseTail (c + 1) T y = stableCorrectedRemainder y -
      ∫ s in 0..T, stableRescaledResidualRate (c + 1) s y := by
  have hcont := (continuousOn_stableRescaledResidualRate_derivatives hc hy.1.le hy.2.1.le hy.2.2.le).1
  have hint : IntervalIntegrable (fun s => stableRescaledResidualRate (c + 1) s y) volume 0 T :=
    (hcont.mono (fun _ ht => ht.1)).intervalIntegrable_of_Icc hT
  have H := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s hs => hasDerivAt_stableCorrectedPhase_rescaled hc hy.1.le hy.2.1.le hy.2.2.le
      (show 0 ≤ s from (uIcc_of_le hT ▸ hs).1)) hint
  simp only [stableRescaledFlow_initial] at H
  rw [H]
  unfold stableCorrectedPhaseTail stableCorrectedRemainder
  ring

end BianchiIX
