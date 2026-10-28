import BianchiIX.Dynamics.StableProjectiveCutoff
import BianchiIX.Dynamics.StableCorrectedTailIdentification
import BianchiIX.Analysis.VariableEndpointSecondDerivative

noncomputable section

namespace BianchiIX

open Set Filter MeasureTheory
open scoped Topology

/-- Original time divided by `c + 1`, at a prescribed projective clock. -/
def stableProjectiveTailTime (c σ : ℝ) (y : StableState) : ℝ :=
  stableProjectiveCutoff c (y, σ) / (c + 1)

def stableJointPhaseTail (c : ℝ) (p : StableState × ℝ) : ℝ :=
  stableCorrectedPhaseTail (c + 1) p.2 p.1

def stableProjectiveTail (c σ : ℝ) (y : StableState) : ℝ :=
  stableJointPhaseTail c (y, stableProjectiveTailTime c σ y)

theorem stableProjectiveTailTime_nonneg {c σ : ℝ} {y : StableState}
    (hc : 2 ≤ c) (hy : y ∈ stableParameterDomain c) (hσ : 0 ≤ σ) :
    0 ≤ stableProjectiveTailTime c σ y :=
  div_nonneg (stableProjectiveCutoff_spec hc hy hσ).1 (by linarith)

theorem contDiffAt_stableProjectiveTailTime_two {c σ : ℝ} {y : StableState}
    (hc : 2 ≤ c) (hy : y ∈ stableParameterDomain c) (hσ : 0 ≤ σ) :
    ContDiffAt ℝ 2 (stableProjectiveTailTime c σ) y :=
  (contDiffAt_stableProjectiveCutoff_initial_two hc hy hσ).div_const _

theorem stableProjectiveTail_eq_original {c σ : ℝ} (hc : 2 ≤ c) (y : StableState) :
    stableProjectiveTail c σ y = stableBoundaryProjection (y 0) (y 1) (y 2) -
      stableCorrectedApproximation y (stableProjectiveCutoff c (y, σ)) := by
  have hK : c + 1 ≠ 0 := by linarith
  unfold stableProjectiveTail stableJointPhaseTail stableCorrectedPhaseTail
    stableRescaledFlow stableProjectiveTailTime
  rw [mul_div_cancel₀ _ hK]
  simp [stableOriginalFlow_eq, stableRestriction_apply, stableCorrectedApproximation]

theorem stableProjectiveTail_zero {c : ℝ} {y : StableState}
    (hc : 2 ≤ c) (hy : y ∈ stableParameterDomain c) :
    stableProjectiveTail c 0 y = stableCorrectedRemainder y := by
  simp only [stableProjectiveTail, stableJointPhaseTail, stableProjectiveTailTime,
    stableProjectiveCutoff_zero hc hy, zero_div, stableCorrectedPhaseTail_zero]

theorem stableProjectiveTail_eq_remainder_sub_integral {c σ : ℝ} {y : StableState}
    (hc : 2 ≤ c) (hy : y ∈ stableParameterDomain c) (hσ : 0 ≤ σ) :
    stableProjectiveTail c σ y = stableCorrectedRemainder y -
      ∫ s in 0..stableProjectiveTailTime c σ y, stableRescaledResidualRate (c + 1) s y :=
  stableCorrectedPhaseTail_eq_remainder_sub_integral hc hy
    (stableProjectiveTailTime_nonneg hc hy hσ)

theorem contDiffAt_stableJointPhaseTail_two {c s : ℝ} {y : StableState}
    (hc : 2 ≤ c) (hy : y ∈ stableParameterDomain c) (hs : 0 ≤ s) :
    ContDiffAt ℝ 2 (stableJointPhaseTail c) (y, s) := by
  have hK : 0 < c + 1 := by linarith
  have hP := (contDiffAt_stableBoundaryProjection_two_in_band hc hy.1 hy.2.1 hy.2.2).comp
    (y, s) (f := Prod.fst) contDiffAt_fst
  have hM : 1 < stableRescaledFlow (c + 1) y s 0 := by
    have H := (abs_le.mp (stableRescaledFlow_band hc hy.1.le hy.2.1.le hy.2.2.le hs).1).1
    linarith
  have hF := (contDiffAt_stableCorrectedPhase 2 hM).comp (y, s)
    (contDiffAt_stableRescaledFlow_two hK hc hy.1.le hy.2.1.le hy.2.2.le hs)
  exact hP.sub hF

theorem hasDerivAt_stableJointPhaseTail_time {c s : ℝ} {y : StableState}
    (hc : 2 ≤ c) (hy : y ∈ stableParameterDomain c) (hs : 0 ≤ s) :
    HasDerivAt (fun r => stableJointPhaseTail c (y, r))
      (-stableRescaledResidualRate (c + 1) s y) s := by
  convert! (hasDerivAt_stableCorrectedPhase_rescaled hc hy.1.le hy.2.1.le hy.2.2.le hs).const_sub
    (stableBoundaryProjection (y 0) (y 1) (y 2)) using 1

theorem contDiffAt_stableProjectiveTail_two {c σ : ℝ} {y : StableState}
    (hc : 2 ≤ c) (hy : y ∈ stableParameterDomain c) (hσ : 0 ≤ σ) :
    ContDiffAt ℝ 2 (stableProjectiveTail c σ) y :=
  (contDiffAt_stableJointPhaseTail_two hc hy (stableProjectiveTailTime_nonneg hc hy hσ)).comp y
    (contDiffAt_id.prodMk (contDiffAt_stableProjectiveTailTime_two hc hy hσ))

/-- Holding projective time fixed introduces an endpoint term in the initial-state derivative. -/
theorem stableProjectiveTail_fderiv_apply {c σ : ℝ} {y : StableState}
    (hc : 2 ≤ c) (hy : y ∈ stableParameterDomain c) (hσ : 0 ≤ σ) (v : StableState) :
    fderiv ℝ (stableProjectiveTail c σ) y v =
      (∫ s in Ioi (stableProjectiveTailTime c σ y),
        fderiv ℝ (stableRescaledResidualRate (c + 1) s) y v) -
      stableRescaledResidualRate (c + 1) (stableProjectiveTailTime c σ y) y *
        fderiv ℝ (stableProjectiveTailTime c σ) y v := by
  have ht := stableProjectiveTailTime_nonneg hc hy hσ
  have H := fderiv_variable_endpoint
    ((contDiffAt_stableJointPhaseTail_two hc hy ht).differentiableAt (by norm_num))
    ((contDiffAt_stableProjectiveTailTime_two hc hy hσ).differentiableAt (by norm_num))
    ((contDiffAt_stableCorrectedPhaseTail_two hc hy ht).differentiableAt (by norm_num)).hasFDerivAt
    (hasDerivAt_stableJointPhaseTail_time hc hy ht) v
  change fderiv ℝ (stableProjectiveTail c σ) y v = _ at H
  rw [stableCorrectedPhaseTail_fderiv_apply hc hy ht] at H
  simpa only [neg_mul, sub_eq_add_neg] using H

theorem stableProjectiveTail_fderiv2_apply {c σ : ℝ} {y : StableState}
    (hc : 2 ≤ c) (hy : y ∈ stableParameterDomain c) (hσ : 0 ≤ σ) (v w : StableState) :
    let τ := stableProjectiveTailTime c σ
    let H := fderiv ℝ (fderiv ℝ (stableJointPhaseTail c)) (y, τ y)
    fderiv ℝ (fderiv ℝ (stableProjectiveTail c σ)) y v w =
      (∫ s in Ioi (τ y), fderiv ℝ (fderiv ℝ (stableRescaledResidualRate (c + 1) s)) y v w) +
      fderiv ℝ τ y v * H (0, 1) (w, 0) +
      fderiv ℝ τ y w * H (v, 0) (0, 1) +
      fderiv ℝ τ y v * fderiv ℝ τ y w * H (0, 1) (0, 1) -
      stableRescaledResidualRate (c + 1) (τ y) y * fderiv ℝ (fderiv ℝ τ) y v w := by
  dsimp only
  have ht := stableProjectiveTailTime_nonneg hc hy hσ
  have hF := contDiffAt_stableJointPhaseTail_two hc hy ht
  have hd := hasDerivAt_stableJointPhaseTail_time hc hy ht
  have H := fderiv2_variable_endpoint hF
    (contDiffAt_stableProjectiveTailTime_two hc hy hσ) hd v w
  have H0 := fderiv2_variable_endpoint
    (τ := fun _ : StableState => stableProjectiveTailTime c σ y) hF contDiffAt_const hd v w
  simp only [fderiv_fun_const, fderiv_zero, Pi.zero_apply, zero_apply, zero_mul, add_zero, mul_zero] at H0
  change fderiv ℝ (fderiv ℝ (stableCorrectedPhaseTail (c + 1) (stableProjectiveTailTime c σ y))) y v w = _ at H0
  rw [← H0, stableCorrectedPhaseTail_fderiv2_apply hc hy ht] at H
  change fderiv ℝ (fderiv ℝ (stableProjectiveTail c σ)) y v w = _ at H
  simpa only [neg_mul, sub_eq_add_neg] using H

end BianchiIX
