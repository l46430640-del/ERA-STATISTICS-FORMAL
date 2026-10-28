import BianchiIX.Dynamics.StableClockVariation
import BianchiIX.Analysis.ParametricVariationIntegral

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

theorem stableClockVariationRate_fderiv_initial {c σ : ℝ} {y : StableState}
    (hc : 2 ≤ c) (hy : y ∈ stableParameterDomain c) (hσ : 0 ≤ σ) (v w : StableState) :
    fderiv ℝ (stableClockVariationRate c w) (y, σ) (v, 0) =
      fderiv ℝ (stableClockField c) (stableClockFlow c (y, σ))
        (fderiv ℝ (fun z => fderiv ℝ (stableClockFlow c) (z, σ) (w, 0)) y v) +
      fderiv ℝ (fderiv ℝ (stableClockField c)) (stableClockFlow c (y, σ))
        (fderiv ℝ (stableClockFlow c) (y, σ) (v, 0))
        (fderiv ℝ (stableClockFlow c) (y, σ) (w, 0)) := by
  have hΦ := contDiffAt_stableClockFlow_two hc hy hσ
  have hFs := (hΦ.differentiableAt (by norm_num)).hasFDerivAt.comp y
    (hasFDerivAt_prodMk_left (𝕜 := ℝ) y σ)
  have hJs : DifferentiableAt ℝ (fun z => fderiv ℝ (stableClockFlow c) (z, σ) (w, 0)) y :=
    ((contDiffAt_parameterVariation hΦ w).differentiableAt (by norm_num)).comp y
      (g := fun p : StableState × ℝ => fderiv ℝ (stableClockFlow c) p (w, 0))
      (f := fun z : StableState => (z, σ))
      ((hasFDerivAt_prodMk_left (𝕜 := ℝ) y σ).differentiableAt)
  have hAs : DifferentiableAt ℝ (fderiv ℝ (stableClockField c)) (stableClockFlow c (y, σ)) :=
    ((contDiff_stableClockField c 2).contDiffAt.fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)
  have Hprod := (hAs.hasFDerivAt.comp y hFs).clm_apply hJs.hasFDerivAt
  have Hpart := ((contDiffAt_stableClockVariationRate_one hc hy hσ w).differentiableAt
    (by norm_num)).hasFDerivAt.comp y (hasFDerivAt_prodMk_left (𝕜 := ℝ) y σ)
  have HE := congrArg (fun L : StableState →L[ℝ] StableState => L v) (Hpart.unique Hprod)
  simpa only [Function.comp_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply,
    add_apply, ContinuousLinearMap.flip_apply] using HE

/-- The ordinary Hessian at fixed projective time solves the forced second variation. -/
theorem exists_stableClockFlow_second_variation {c T : ℝ} {y : StableState}
    (hc : 2 ≤ c) (hy : y ∈ stableParameterDomain c) (v w : StableState) :
    ∃ Q : ℝ → StableState, Q 0 = 0 ∧ ∀ σ ∈ Icc 0 T,
      Q σ = fderiv ℝ (fderiv ℝ (fun z => stableClockFlow c (z, σ))) y v w ∧
      HasDerivAt Q
        (fderiv ℝ (stableClockField c) (stableClockFlow c (y, σ)) (Q σ) +
          fderiv ℝ (fderiv ℝ (stableClockField c)) (stableClockFlow c (y, σ))
            (fderiv ℝ (stableClockFlow c) (y, σ) (v, 0))
            (fderiv ℝ (stableClockFlow c) (y, σ) (w, 0))) σ := by
  have HG (σ : ℝ) (hσ : σ ∈ Icc 0 T) :
      ContDiffAt ℝ 1 (stableClockVariationRate c w) (y, σ) :=
    contDiffAt_stableClockVariationRate_one hc hy hσ.1 w
  have HJ : ∀ᶠ z in 𝓝 y, ∀ σ ∈ Icc 0 T,
      HasDerivAt (fun r => fderiv ℝ (stableClockFlow c) (z, r) (w, 0))
        (stableClockVariationRate c w (z, σ)) σ := by
    filter_upwards [(isOpen_stableParameterDomain c).mem_nhds hy] with z hz σ hσ
    exact hasDerivAt_stableClockFlow_variation hc hz hσ.1 w
  have hi : ∀ᶠ z in 𝓝 y, fderiv ℝ (stableClockFlow c) (z, 0) (w, 0) = w := by
    filter_upwards [(isOpen_stableParameterDomain c).mem_nhds hy] with z hz
    exact stableClockFlow_variation_initial hc hz w
  obtain ⟨Q, hQ0, HQ⟩ := exists_parametric_variation_integral
    (J := fun p : StableState × ℝ => fderiv ℝ (stableClockFlow c) p (w, 0))
    (G := stableClockVariationRate c w) HG HJ hi v
  refine ⟨Q, hQ0, ?_⟩
  intro σ hσ
  refine ⟨(HQ σ hσ).1.trans
    (fderiv_parameterVariation_apply (contDiffAt_stableClockFlow_two hc hy hσ.1) v w), ?_⟩
  have HD := (HQ σ hσ).2
  rwa [stableClockVariationRate_fderiv_initial hc hy hσ.1 v w, ← (HQ σ hσ).1] at HD

end BianchiIX
