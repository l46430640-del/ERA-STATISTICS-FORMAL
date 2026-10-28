import BianchiIX.Analysis.CoordinateVariation
import BianchiIX.Dynamics.ProjectiveOriginalTime
import BianchiIX.Dynamics.FlowTransport

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

def projectiveOriginalFlow (y : ProjectiveState) (t₀ t : ℝ) : ProjectiveState :=
  toProjectiveState (normalizedMaxCurve (fromProjectiveState y) t₀ t)

def projectiveFlowDifferential (y : ProjectiveState) (t₀ t : ℝ) :
    ProjectiveState →L[ℝ] ProjectiveState :=
  (fderiv ℝ toProjectiveState (normalizedMaxCurve (fromProjectiveState y) t₀ t)).comp
    ((normalizedFlowDifferential (fromProjectiveState y) t₀ t).comp (fderiv ℝ fromProjectiveState y))

theorem projective_chart_differential_inverse {y : ProjectiveState}
    (hD : 0 < projectiveStateDenom y) :
    (fderiv ℝ toProjectiveState (fromProjectiveState y)).comp (fderiv ℝ fromProjectiveState y) =
      ContinuousLinearMap.id ℝ ProjectiveState := by
  have hfrom := ((contDiffAt_fromProjectiveState 1 (ne_of_gt hD)).differentiableAt (by norm_num)).hasFDerivAt
  have hto := ((contDiffAt_toProjectiveState 1 (ne_of_gt (fromProjectiveState_clock_pos hD))).differentiableAt
    (by norm_num)).hasFDerivAt
  have heq : (fun z => toProjectiveState (fromProjectiveState z)) =ᶠ[𝓝 y] id := by
    filter_upwards [continuous_projectiveStateDenom.continuousAt.eventually_ne (ne_of_gt hD)] with z hz
    exact toProjectiveState_fromProjectiveState hz
  exact ((hto.comp y hfrom).congr_of_eventuallyEq heq.symm).unique (hasFDerivAt_id y)

theorem projectiveOriginalFlow_initial {y : ProjectiveState} (hD : 0 < projectiveStateDenom y) (t₀ : ℝ) :
    projectiveOriginalFlow y t₀ t₀ = y := by
  rw [projectiveOriginalFlow, normalizedMaxCurve_initial]
  exact toProjectiveState_fromProjectiveState (ne_of_gt hD)

theorem projectiveFlowDifferential_initial {y : ProjectiveState} (hD : 0 < projectiveStateDenom y) (t₀ : ℝ) :
    projectiveFlowDifferential y t₀ t₀ = ContinuousLinearMap.id ℝ ProjectiveState := by
  rw [projectiveFlowDifferential, normalizedMaxCurve_initial, normalizedFlowDifferential_initial,
    ContinuousLinearMap.id_comp, projective_chart_differential_inverse hD]

theorem hasFDerivAt_projectiveOriginalFlow_initial {y : ProjectiveState} {t₀ t : ℝ}
    (hD : 0 < projectiveStateDenom y) (ht : t ∈ normalizedMaxDomain (fromProjectiveState y) t₀)
    (hA : 0 < 1 + normalizedMaxCurve (fromProjectiveState y) t₀ t 0) :
    HasFDerivAt (fun z => projectiveOriginalFlow z t₀ t) (projectiveFlowDifferential y t₀ t) y := by
  have hfrom := ((contDiffAt_fromProjectiveState 1 (ne_of_gt hD)).differentiableAt (by norm_num)).hasFDerivAt
  have hto := ((contDiffAt_toProjectiveState 1 (ne_of_gt hA)).differentiableAt (by norm_num)).hasFDerivAt
  exact hto.comp y ((hasFDerivAt_normalizedMaxCurve_initial ht).comp y hfrom)

theorem hasDerivAt_projectiveOriginalFlow_time {y : ProjectiveState} {t₀ t : ℝ}
    (hD : 0 < projectiveStateDenom y) (ht : t ∈ normalizedMaxDomain (fromProjectiveState y) t₀)
    (hA : 0 < 1 + normalizedMaxCurve (fromProjectiveState y) t₀ t 0) :
    HasDerivAt (projectiveOriginalFlow y t₀)
      (projectiveOriginalField (projectiveOriginalFlow y t₀ t)) t := by
  have hc : stateConstraint (normalizedMaxCurve (fromProjectiveState y) t₀ t) = 1 :=
    (normalizedMaxCurve_constraint ht).trans (fromProjectiveState_constraint (ne_of_gt hD))
  exact hasDerivAt_projectiveOriginalFlow (hasDerivAt_normalizedMaxCurve ht) (ne_of_gt hA) hc

/-- The actual initial-state derivative satisfies the reduced variational equation. -/
theorem hasDerivAt_projectiveFlowDifferential_apply {y : ProjectiveState} {t₀ t : ℝ}
    (hD : 0 < projectiveStateDenom y) (ht : t ∈ normalizedMaxDomain (fromProjectiveState y) t₀)
    (hA : 0 < 1 + normalizedMaxCurve (fromProjectiveState y) t₀ t 0) (w : ProjectiveState) :
    HasDerivAt (fun s => projectiveFlowDifferential y t₀ s w)
      (fderiv ℝ projectiveOriginalField (projectiveOriginalFlow y t₀ t)
        (projectiveFlowDifferential y t₀ t w)) t := by
  let alpha := normalizedMaxCurve (fromProjectiveState y) t₀
  let b : ProjectiveState → NormalizedState := fun z => normalizedMaxCurve (fromProjectiveState z) t₀ t
  let v : ℝ → NormalizedState := fun s => normalizedFlowDifferential (fromProjectiveState y) t₀ s
    (fderiv ℝ fromProjectiveState y w)
  have hfrom := ((contDiffAt_fromProjectiveState 1 (ne_of_gt hD)).differentiableAt (by norm_num)).hasFDerivAt
  have hb := (hasFDerivAt_normalizedMaxCurve_initial ht).comp y hfrom
  have hv : HasDerivAt v (fderiv ℝ normalizedField (alpha t) (v t)) t := by
    simpa only [v, alpha, normalizedDifferential, ContinuousLinearMap.comp_apply, map_zero, add_zero] using
      (hasDerivAt_normalizedFlowDifferential ht).clm_apply
        (hasDerivAt_const t (fderiv ℝ fromProjectiveState y w))
  have hc : stateConstraint (alpha t) = 1 :=
    (normalizedMaxCurve_constraint ht).trans (fromProjectiveState_constraint (ne_of_gt hD))
  have heq : (fun z => fderiv ℝ toProjectiveState (b z) (normalizedField (b z)))
      =ᶠ[𝓝 y] (fun z => projectiveOriginalField (toProjectiveState (b z))) := by
    have hdomain : ∀ᶠ z in 𝓝 y, t ∈ normalizedMaxDomain (fromProjectiveState z) t₀ :=
      (hfrom.continuousAt.prodMk continuousAt_const).eventually
        ((isOpen_normalizedFlowDomain t₀).mem_nhds ht)
    have hclock : ∀ᶠ z in 𝓝 y, 1 + b z 0 ≠ 0 :=
      (continuousAt_const.add ((continuous_apply 0).continuousAt.comp hb.continuousAt)).eventually_ne
        (ne_of_gt hA)
    filter_upwards [hdomain, hclock,
      continuous_projectiveStateDenom.continuousAt.eventually_ne (ne_of_gt hD)] with z hz hAz hDz
    have hcz : stateConstraint (b z) = 1 :=
      (normalizedMaxCurve_constraint hz).trans (fromProjectiveState_constraint hDz)
    rw [toProjectiveState_fderiv_field hAz hcz]
    have hs : 6 / projectiveStateDenom (toProjectiveState (b z)) = 1 + b z 0 :=
      projective_inverse_scale hAz hcz
    rw [projectiveOriginalField, hs]
  exact hasDerivAt_coordinate_variation (contDiffAt_toProjectiveState 2 (ne_of_gt hA))
    ((contDiff_normalizedField 1).differentiable (by norm_num) (alpha t))
    ((contDiffAt_projectiveOriginalField 1 (ne_of_gt (toProjectiveState_denom_pos hA hc))).differentiableAt
      (by norm_num))
    (hasDerivAt_normalizedMaxCurve ht) hv hb rfl rfl heq

end BianchiIX
