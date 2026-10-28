import BianchiIX.Dynamics.StableSecondSource
import BianchiIX.Dynamics.StableProjectionFirstRegularity
import BianchiIX.Analysis.IntegralVariation

noncomputable section

namespace BianchiIX

open Set Filter MeasureTheory
open scoped Topology

def stableSecondIntegral (K : ℝ) (y w : StableState) (s : ℝ) : StableState →L[ℝ] StableState :=
  ∫ r in 0..s, (fderiv ℝ (stableRescaledVariationRate K w) (y, r)).comp
    (ContinuousLinearMap.inl ℝ StableState ℝ)

theorem stableRescaledFlow_fderiv2 {K : ℝ} {y : StableState} {c s : ℝ}
    (hK : 0 < K) (hc : 2 ≤ c) (hm : |y 0 - c| < 1 / 40)
    (hu : |y 1| < 1 / 200) (hw : |y 2| < 1 / 200) (hs : 0 ≤ s) :
    fderiv ℝ (fderiv ℝ (fun z => stableRescaledFlow K z s)) y =
      stableRescaledSecondDifferential K y s := by
  have heq : fderiv ℝ (fun z => stableRescaledFlow K z s) =ᶠ[𝓝 y]
      (fun z => stableRescaledDifferential K z s) := by
    filter_upwards [(isOpen_stableParameterDomain c).mem_nhds ⟨hm, hu, hw⟩] with z hz
    exact (hasFDerivAt_stableRescaledFlow hK hc hz.1.le hz.2.1.le hz.2.2.le hs).fderiv
  rw [heq.fderiv_eq]
  exact (hasFDerivAt_stableRescaledDifferential hK hc hm.le hu.le hw.le hs).fderiv

theorem stableRescaledSecondDifferential_eq_integral {K : ℝ} {y : StableState} {c s : ℝ}
    (hK : 0 < K) (hc : 2 ≤ c) (hm : |y 0 - c| < 1 / 40)
    (hu : |y 1| < 1 / 200) (hw : |y 2| < 1 / 200) (hs : 0 ≤ s) (v w : StableState) :
    stableRescaledSecondDifferential K y s v w = stableSecondIntegral K y w s v := by
  have hG (r : ℝ) (hr : r ∈ Icc 0 s) :
      ContDiffAt ℝ 1 (stableRescaledVariationRate K w) (y, r) :=
    contDiffAt_stableRescaledVariationRate_one hK hc hm.le hu.le hw.le hr.1 w
  have hJ : ∀ᶠ z in 𝓝 y, ∀ r ∈ Icc 0 s,
      HasDerivAt (fun a => stableRescaledDifferential K z a w)
        (stableRescaledVariationRate K w (z, r)) r := by
    filter_upwards [(isOpen_stableParameterDomain c).mem_nhds ⟨hm, hu, hw⟩] with z hz
    intro r hr
    simpa only [stableRescaledVariationRate, stableOriginalField_fderiv] using
      stableRescaledFlow_variational_equation hK hc hz.1.le hz.2.1.le hz.2.2.le hr.1 w
  have hi : ∀ᶠ z in 𝓝 y, stableRescaledDifferential K z 0 w = w := by
    filter_upwards [] with z
    simp only [stableRescaledDifferential_initial, ContinuousLinearMap.id_apply]
  have H := hasFDerivAt_of_parametric_ode
    (J := fun p : StableState × ℝ => stableRescaledDifferential K p.1 p.2 w)
    (v := w) hs hG hJ hi
  have hactual := (hasFDerivAt_stableRescaledDifferential hK hc hm.le hu.le hw.le hs).clm_apply
    (hasFDerivAt_const w y)
  have Heq := congrArg (fun L : StableState →L[ℝ] StableState => L v) (hactual.unique H)
  simpa only [ContinuousLinearMap.comp_apply, add_apply, zero_apply, map_zero, zero_add,
    ContinuousLinearMap.flip_apply, stableSecondIntegral] using Heq

theorem stableRescaledSecondDifferential_integral_equation {K : ℝ} {y : StableState} {c s : ℝ}
    (hK : 0 < K) (hc : 2 ≤ c) (hm : |y 0 - c| < 1 / 40)
    (hu : |y 1| < 1 / 200) (hw : |y 2| < 1 / 200) (hs : 0 ≤ s) (v w : StableState) :
    stableRescaledSecondDifferential K y s v w =
      ∫ r in 0..s, stableRescaledSecondSource K v w (y, r) := by
  rw [stableRescaledSecondDifferential_eq_integral hK hc hm hu hw hs v w, stableSecondIntegral]
  have hcont : ContinuousOn (fun r =>
      (fderiv ℝ (stableRescaledVariationRate K w) (y, r)).comp
        (ContinuousLinearMap.inl ℝ StableState ℝ)) (Icc 0 s) := by
    intro r hr
    exact (((contDiffAt_stableRescaledVariationRate_one hK hc hm.le hu.le hw.le hr.1 w).continuousAt_fderiv
      (by norm_num)).clm_comp continuousAt_const |>.comp
      (continuousAt_const.prodMk continuousAt_id)).continuousWithinAt
  rw [ContinuousLinearMap.intervalIntegral_apply (hcont.intervalIntegrable_of_Icc hs)]
  apply intervalIntegral.integral_congr
  intro r hr
  exact stableRescaledVariationRate_fderiv_initial hK hc hm.le hu.le hw.le
    (uIcc_of_le hs ▸ hr).1 v w

theorem hasDerivAt_stableSecondIntegral_apply {K : ℝ} {y : StableState} {c s : ℝ}
    (hK : 0 < K) (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 40)
    (hu : |y 1| ≤ 1 / 200) (hw : |y 2| ≤ 1 / 200) (hs : 0 ≤ s) (v w : StableState) :
    HasDerivAt (fun r => stableSecondIntegral K y w r v)
      (stableRescaledSecondSource K v w (y, s)) s := by
  have H := hasDerivAt_integral_partial_fderiv hs
    (fun r hr => contDiffAt_stableRescaledVariationRate_one hK hc hm hu hw hr.1 w)
  have Hv := H.clm_apply (hasDerivAt_const s v)
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply, map_zero, add_zero,
    stableRescaledVariationRate_fderiv_initial hK hc hm hu hw hs v w, stableSecondIntegral] using Hv

end BianchiIX
