import BianchiIX.Analysis.ClockVariation
import BianchiIX.Dynamics.ConnectionClockDifferential
import BianchiIX.Dynamics.ProjectiveFlowVariation

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

/-- Tangent at fixed log(W/W_entry); zeta is the initial logarithmic wall variation. -/
def connectionClockProjection (y v : ProjectiveState) (ζ : ℝ) : ProjectiveState :=
  v - (v 3 / y 3 - ζ) • connectionLogField y

theorem connectionClockProjection_wall {y v : ProjectiveState} {ζ : ℝ}
    (hD : connectionClockRate y ≠ 0) (hw : y 3 ≠ 0) :
    connectionClockProjection y v ζ 3 = ζ * y 3 := by
  change v 3 - (v 3 / y 3 - ζ) * connectionLogField y 3 = _
  rw [(connectionLogField_components hD).2.2.2]
  field_simp
  ring

theorem hasDerivAt_connectionClockProjection {β v : ℝ → ProjectiveState} {t ζ : ℝ}
    (hβ : HasDerivAt β (projectiveOriginalField (β t)) t)
    (hv : HasDerivAt v (fderiv ℝ projectiveOriginalField (β t) (v t)) t)
    (hw : β t 3 ≠ 0) (hden : projectiveStateDenom (β t) ≠ 0)
    (hD : connectionClockRate (β t) ≠ 0) :
    HasDerivAt (fun s => connectionClockProjection (β s) (v s) ζ)
      (connectionOriginalClockRate (β t) • fderiv ℝ connectionLogField (β t)
        (connectionClockProjection (β t) (v t) ζ)) t := by
  have hF := (contDiffAt_connectionLogField 1 hD).differentiableAt (by norm_num)
  have hwnear : ∀ᶠ y : ProjectiveState in 𝓝 (β t), y 3 ≠ 0 :=
    (continuous_apply 3).continuousAt.eventually_ne hw
  have hDnear : ∀ᶠ y : ProjectiveState in 𝓝 (β t), connectionClockRate y ≠ 0 :=
    (contDiff_connectionClockRate 1).continuous.continuousAt.eventually_ne hD
  have hclock : (fun y => fderiv ℝ connectionLogClock y (projectiveOriginalField y))
      =ᶠ[𝓝 (β t)] connectionOriginalClockRate := by
    filter_upwards [hwnear] with y hy
    exact connectionLogClock_fderiv_field hy
  have hstate : (fun y => fderiv ℝ (id : ProjectiveState → ProjectiveState) y (projectiveOriginalField y))
      =ᶠ[𝓝 (β t)] (fun y => connectionOriginalClockRate y • connectionLogField y) := by
    filter_upwards [hDnear] with y hy
    simpa only [fderiv_id, ContinuousLinearMap.id_apply] using projectiveOriginalField_connectionLog hy
  have hfield : DifferentiableAt ℝ (fun q : ℝ × ProjectiveState => connectionLogField q.2)
      (connectionLogClock (β t), β t) := by
    fun_prop
  have H := hasDerivAt_coordinate_clock_variation (p := id)
    (field := fun q : ℝ × ProjectiveState => connectionLogField q.2)
    contDiffAt_id (contDiffAt_connectionLogClock 2 hw)
    ((contDiffAt_projectiveOriginalField 1 hden).differentiableAt (by norm_num))
    ((contDiffAt_connectionOriginalClockRate 1 hden).differentiableAt (by norm_num))
    hfield hβ hv hclock hstate
  simp only [fderiv_id, ContinuousLinearMap.id_apply, id_eq] at H
  have hζ := (hF.hasFDerivAt.comp_hasDerivAt t hβ).const_smul ζ
  have heq : (fun s => connectionClockProjection (β s) (v s) ζ) =ᶠ[𝓝 t]
      (fun s => v s - fderiv ℝ connectionLogClock (β s) (v s) • connectionLogField (β s) +
        ζ • connectionLogField (β s)) := by
    filter_upwards [hβ.continuousAt.eventually hwnear] with s hs
    rw [connectionClockProjection, connectionLogClock_fderiv hs, sub_smul]
    module
  apply ((H.add hζ).congr_of_eventuallyEq heq).congr_deriv
  simp only [projectiveOriginalField_connectionLog hD, connectionClockProjection,
    connectionLogClock_fderiv hw, map_sub, map_smul]
  module

def connectionProjectedFlowVariation (y : ProjectiveState) (t₀ t : ℝ) (w : ProjectiveState) :
    ProjectiveState := connectionClockProjection (projectiveOriginalFlow y t₀ t)
      (projectiveFlowDifferential y t₀ t w) (w 3 / y 3)

theorem connectionProjectedFlowVariation_initial {y : ProjectiveState}
    (hD : 0 < projectiveStateDenom y) (t₀ : ℝ) (w : ProjectiveState) :
    connectionProjectedFlowVariation y t₀ t₀ w = w := by
  rw [connectionProjectedFlowVariation, projectiveOriginalFlow_initial hD,
    projectiveFlowDifferential_initial hD, ContinuousLinearMap.id_apply]
  simp [connectionClockProjection]

theorem hasDerivAt_connectionProjectedFlowVariation {y : ProjectiveState} {t₀ t : ℝ}
    (hD : 0 < projectiveStateDenom y) (ht : t ∈ normalizedMaxDomain (fromProjectiveState y) t₀)
    (hA : 0 < 1 + normalizedMaxCurve (fromProjectiveState y) t₀ t 0)
    (hw : projectiveOriginalFlow y t₀ t 3 ≠ 0)
    (hclock : connectionClockRate (projectiveOriginalFlow y t₀ t) ≠ 0) (w : ProjectiveState) :
    HasDerivAt (fun s => connectionProjectedFlowVariation y t₀ s w)
      (connectionOriginalClockRate (projectiveOriginalFlow y t₀ t) •
        fderiv ℝ connectionLogField (projectiveOriginalFlow y t₀ t)
          (connectionProjectedFlowVariation y t₀ t w)) t := by
  have hc : stateConstraint (normalizedMaxCurve (fromProjectiveState y) t₀ t) = 1 :=
    (normalizedMaxCurve_constraint ht).trans (fromProjectiveState_constraint (ne_of_gt hD))
  exact hasDerivAt_connectionClockProjection (hasDerivAt_projectiveOriginalFlow_time hD ht hA)
    (hasDerivAt_projectiveFlowDifferential_apply hD ht hA w) hw
    (ne_of_gt (toProjectiveState_denom_pos hA hc)) hclock

theorem hasDerivAt_connectionProjectedFlowVariation_log {y : ProjectiveState} {t₀ z : ℝ}
    {q : ℝ → ℝ} (hD : 0 < projectiveStateDenom y)
    (ht : q z ∈ normalizedMaxDomain (fromProjectiveState y) t₀)
    (hA : 0 < 1 + normalizedMaxCurve (fromProjectiveState y) t₀ (q z) 0)
    (hw : projectiveOriginalFlow y t₀ (q z) 3 ≠ 0)
    (hclock : connectionClockRate (projectiveOriginalFlow y t₀ (q z)) ≠ 0)
    (hq : HasDerivAt q (1 / connectionOriginalClockRate (projectiveOriginalFlow y t₀ (q z))) z)
    (w : ProjectiveState) :
    HasDerivAt (fun r => connectionProjectedFlowVariation y t₀ (q r) w)
      (fderiv ℝ connectionLogField (projectiveOriginalFlow y t₀ (q z))
        (connectionProjectedFlowVariation y t₀ (q z) w)) z := by
  have hc : stateConstraint (normalizedMaxCurve (fromProjectiveState y) t₀ (q z)) = 1 :=
    (normalizedMaxCurve_constraint ht).trans (fromProjectiveState_constraint (ne_of_gt hD))
  have hr : connectionOriginalClockRate (projectiveOriginalFlow y t₀ (q z)) ≠ 0 :=
    mul_ne_zero (div_ne_zero (by norm_num) (ne_of_gt (toProjectiveState_denom_pos hA hc))) hclock
  have H := (hasDerivAt_connectionProjectedFlowVariation hD ht hA hw hclock w).scomp z hq
  simpa only [Function.comp_def, smul_smul, one_div_mul_cancel hr, one_smul] using H

end BianchiIX
