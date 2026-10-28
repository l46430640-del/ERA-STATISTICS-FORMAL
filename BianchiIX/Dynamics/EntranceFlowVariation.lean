import BianchiIX.Analysis.ClockVariation
import BianchiIX.Dynamics.EntranceClockDifferential
import BianchiIX.Dynamics.ProjectiveFlowVariation

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

/-- Tangent at fixed log(V/V_entry); zeta is the initial logarithmic wall variation. -/
def entranceClockProjection (y v : ProjectiveState) (ζ : ℝ) : ProjectiveState :=
  v - (v 2 / y 2 - ζ) • entranceLogField y

theorem entranceClockProjection_active {y v : ProjectiveState} {ζ : ℝ}
    (hD : entranceClockRate y ≠ 0) (hv : y 2 ≠ 0) :
    entranceClockProjection y v ζ 2 = ζ * y 2 := by
  change v 2 - (v 2 / y 2 - ζ) * entranceLogField y 2 = _
  rw [entranceLogField_active hD]
  field_simp
  ring

theorem hasDerivAt_entranceClockProjection {β v : ℝ → ProjectiveState} {t ζ : ℝ}
    (hβ : HasDerivAt β (projectiveOriginalField (β t)) t)
    (hv : HasDerivAt v (fderiv ℝ projectiveOriginalField (β t) (v t)) t)
    (hw : β t 2 ≠ 0) (hden : projectiveStateDenom (β t) ≠ 0)
    (hD : entranceClockRate (β t) ≠ 0) :
    HasDerivAt (fun s => entranceClockProjection (β s) (v s) ζ)
      (entranceOriginalClockRate (β t) • fderiv ℝ entranceLogField (β t)
        (entranceClockProjection (β t) (v t) ζ)) t := by
  have hF := (contDiffAt_entranceLogField 1 hD).differentiableAt (by norm_num)
  have hwnear : ∀ᶠ y : ProjectiveState in 𝓝 (β t), y 2 ≠ 0 :=
    (continuous_apply 2).continuousAt.eventually_ne hw
  have hDnear : ∀ᶠ y : ProjectiveState in 𝓝 (β t), entranceClockRate y ≠ 0 :=
    continuous_entranceClockRate.continuousAt.eventually_ne hD
  have hclock : (fun y => fderiv ℝ entranceLogClock y (projectiveOriginalField y))
      =ᶠ[𝓝 (β t)] entranceOriginalClockRate := by
    filter_upwards [hwnear] with y hy
    exact entranceLogClock_fderiv_field hy
  have hstate : (fun y => fderiv ℝ (id : ProjectiveState → ProjectiveState) y (projectiveOriginalField y))
      =ᶠ[𝓝 (β t)] (fun y => entranceOriginalClockRate y • entranceLogField y) := by
    filter_upwards [hDnear] with y hy
    simpa only [fderiv_id, ContinuousLinearMap.id_apply] using projectiveOriginalField_entranceLog hy
  have hfield : DifferentiableAt ℝ (fun q : ℝ × ProjectiveState => entranceLogField q.2)
      (entranceLogClock (β t), β t) := by fun_prop
  have H := hasDerivAt_coordinate_clock_variation (p := id)
    (field := fun q : ℝ × ProjectiveState => entranceLogField q.2)
    contDiffAt_id (contDiffAt_entranceLogClock 2 hw)
    ((contDiffAt_projectiveOriginalField 1 hden).differentiableAt (by norm_num))
    ((contDiffAt_entranceOriginalClockRate 1 hden).differentiableAt (by norm_num))
    hfield hβ hv hclock hstate
  simp only [fderiv_id, ContinuousLinearMap.id_apply, id_eq] at H
  have hζ := (hF.hasFDerivAt.comp_hasDerivAt t hβ).const_smul ζ
  have heq : (fun s => entranceClockProjection (β s) (v s) ζ) =ᶠ[𝓝 t]
      (fun s => v s - fderiv ℝ entranceLogClock (β s) (v s) • entranceLogField (β s) +
        ζ • entranceLogField (β s)) := by
    filter_upwards [hβ.continuousAt.eventually hwnear] with s hs
    rw [entranceClockProjection, entranceLogClock_fderiv hs, sub_smul]
    module
  apply ((H.add hζ).congr_of_eventuallyEq heq).congr_deriv
  simp only [projectiveOriginalField_entranceLog hD, entranceClockProjection,
    entranceLogClock_fderiv hw, map_sub, map_smul]
  module

def entranceProjectedFlowVariation (y : ProjectiveState) (t₀ t : ℝ) (w : ProjectiveState) :
    ProjectiveState := entranceClockProjection (projectiveOriginalFlow y t₀ t)
      (projectiveFlowDifferential y t₀ t w) (w 2 / y 2)

theorem entranceProjectedFlowVariation_initial {y : ProjectiveState}
    (hD : 0 < projectiveStateDenom y) (t₀ : ℝ) (w : ProjectiveState) :
    entranceProjectedFlowVariation y t₀ t₀ w = w := by
  rw [entranceProjectedFlowVariation, projectiveOriginalFlow_initial hD,
    projectiveFlowDifferential_initial hD, ContinuousLinearMap.id_apply]
  simp [entranceClockProjection]

theorem hasDerivAt_entranceProjectedFlowVariation {y : ProjectiveState} {t₀ t : ℝ}
    (hD : 0 < projectiveStateDenom y) (ht : t ∈ normalizedMaxDomain (fromProjectiveState y) t₀)
    (hA : 0 < 1 + normalizedMaxCurve (fromProjectiveState y) t₀ t 0)
    (hw : projectiveOriginalFlow y t₀ t 2 ≠ 0)
    (hclock : entranceClockRate (projectiveOriginalFlow y t₀ t) ≠ 0) (w : ProjectiveState) :
    HasDerivAt (fun s => entranceProjectedFlowVariation y t₀ s w)
      (entranceOriginalClockRate (projectiveOriginalFlow y t₀ t) •
        fderiv ℝ entranceLogField (projectiveOriginalFlow y t₀ t)
          (entranceProjectedFlowVariation y t₀ t w)) t := by
  have hc : stateConstraint (normalizedMaxCurve (fromProjectiveState y) t₀ t) = 1 :=
    (normalizedMaxCurve_constraint ht).trans (fromProjectiveState_constraint (ne_of_gt hD))
  exact hasDerivAt_entranceClockProjection (hasDerivAt_projectiveOriginalFlow_time hD ht hA)
    (hasDerivAt_projectiveFlowDifferential_apply hD ht hA w) hw
    (ne_of_gt (toProjectiveState_denom_pos hA hc)) hclock

theorem entranceProjectedFlowVariation_active {y : ProjectiveState} {t₀ t : ℝ}
    (hv : projectiveOriginalFlow y t₀ t 2 ≠ 0)
    (hD : entranceClockRate (projectiveOriginalFlow y t₀ t) ≠ 0) (w : ProjectiveState) :
    entranceProjectedFlowVariation y t₀ t w 2 = (w 2 / y 2) * projectiveOriginalFlow y t₀ t 2 :=
  entranceClockProjection_active hD hv

end BianchiIX
