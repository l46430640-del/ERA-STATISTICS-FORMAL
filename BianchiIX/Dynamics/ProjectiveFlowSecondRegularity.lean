import BianchiIX.Dynamics.ProjectiveFlowVariation
import BianchiIX.Dynamics.FlowSecondRegularity

noncomputable section

namespace BianchiIX

open Set

theorem contDiffAt_projectiveOriginalFlow_two {y : ProjectiveState} {t₀ t : ℝ}
    (hD : 0 < projectiveStateDenom y) (ht : t ∈ normalizedMaxDomain (fromProjectiveState y) t₀)
    (hA : 0 < 1 + normalizedMaxCurve (fromProjectiveState y) t₀ t 0) :
    ContDiffAt ℝ 2 (fun z : ProjectiveState × ℝ => projectiveOriginalFlow z.1 t₀ z.2) (y, t) := by
  have hparam : ContDiffAt ℝ 2 (fun z : ProjectiveState × ℝ => (fromProjectiveState z.1, z.2)) (y, t) :=
    ((contDiffAt_fromProjectiveState 2 (ne_of_gt hD)).comp (y, t) contDiffAt_fst).prodMk contDiffAt_snd
  have hN : ContDiffAt ℝ 2 (fun z : ProjectiveState × ℝ => normalizedMaxCurve (fromProjectiveState z.1) t₀ z.2) (y, t) := by
    simpa only [Function.comp_def] using (contDiffAt_normalizedMaxCurve_two ht).comp (y, t) hparam
  simpa only [Function.comp_def, projectiveOriginalFlow] using
    (contDiffAt_toProjectiveState 2 (ne_of_gt hA)).comp (y, t) hN

theorem hasFDerivAt_projectiveOriginalFlow {y : ProjectiveState} {t₀ t : ℝ}
    (hD : 0 < projectiveStateDenom y) (ht : t ∈ normalizedMaxDomain (fromProjectiveState y) t₀)
    (hA : 0 < 1 + normalizedMaxCurve (fromProjectiveState y) t₀ t 0) :
    HasFDerivAt (fun z : ProjectiveState × ℝ => projectiveOriginalFlow z.1 t₀ z.2)
      ((projectiveFlowDifferential y t₀ t).coprod
        ((ContinuousLinearMap.id ℝ ℝ).smulRight (projectiveOriginalField (projectiveOriginalFlow y t₀ t)))) (y, t) := by
  have H := ((contDiffAt_projectiveOriginalFlow_two hD ht hA).differentiableAt (by norm_num)).hasFDerivAt
  have hleft : HasFDerivAt (fun z => projectiveOriginalFlow z t₀ t)
      ((fderiv ℝ (fun z : ProjectiveState × ℝ => projectiveOriginalFlow z.1 t₀ z.2) (y, t)).comp
        (ContinuousLinearMap.inl ℝ ProjectiveState ℝ)) y := by
    simpa only [Function.comp_def] using H.comp y (hasFDerivAt_prodMk_left (𝕜 := ℝ) y t)
  have hright : HasFDerivAt (projectiveOriginalFlow y t₀)
      ((fderiv ℝ (fun z : ProjectiveState × ℝ => projectiveOriginalFlow z.1 t₀ z.2) (y, t)).comp
        (ContinuousLinearMap.inr ℝ ProjectiveState ℝ)) t := by
    simpa only [Function.comp_def] using H.comp t (hasFDerivAt_prodMk_right y t)
  have hl := hleft.unique (hasFDerivAt_projectiveOriginalFlow_initial hD ht hA)
  have hr := hright.unique (hasDerivAt_projectiveOriginalFlow_time hD ht hA).hasFDerivAt
  have heq : ContinuousLinearMap.toSpanSingleton ℝ (projectiveOriginalField (projectiveOriginalFlow y t₀ t)) =
      (ContinuousLinearMap.id ℝ ℝ).smulRight (projectiveOriginalField (projectiveOriginalFlow y t₀ t)) := by
    ext u
    rfl
  rw [heq] at hr
  rw [← hl, ← hr, ContinuousLinearMap.coprod_comp_inl_inr]
  exact H

end BianchiIX
