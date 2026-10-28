import BianchiIX.Analysis.ClockVariation
import BianchiIX.Dynamics.CoreCoordinateDifferential
import BianchiIX.Dynamics.CoreLinearization
import BianchiIX.Dynamics.ProjectiveFlowVariation

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

/-- Remove the angular displacement from a projective tangent vector. -/
def coreClockProjection (y v : ProjectiveState) : CoreAngleState :=
  fderiv ℝ toCoreAngleState y v -
    fderiv ℝ projectiveCoreAngle y v • coreAngleField (projectiveCoreAngle y) (toCoreAngleState y)

def coreProjectedFlowVariation (y : ProjectiveState) (t₀ t : ℝ) (w : ProjectiveState) :
    CoreAngleState :=
  coreClockProjection (projectiveOriginalFlow y t₀ t) (projectiveFlowDifferential y t₀ t w)

theorem coreAuxiliary_projective_clockFactor {y : ProjectiveState} (hv : 0 < y 2) :
    coreAuxiliary (projectiveCoreAngle y) (toCoreAngleState y) 1 =
      coreClockFactor (coreRadius (y 0) (y 2)) (y 1) (y 3) := by
  change coreClockFactor (coreRadius (y 0) (y 2)) (y 1)
    (y 2 * y 3 / (coreRadius (y 0) (y 2) / Real.cosh (coreAngle (y 0) (y 2)))) = _
  rw [(coreAngle_coordinates hv).1, mul_div_cancel_left₀ _ (ne_of_gt hv)]

theorem hasDerivAt_coreClockProjection {beta v : ℝ → ProjectiveState} {t : ℝ}
    (hbeta : HasDerivAt beta (projectiveOriginalField (beta t)) t)
    (hv : HasDerivAt v (fderiv ℝ projectiveOriginalField (beta t) (v t)) t)
    (hV : 0 < beta t 2) (hD : projectiveStateDenom (beta t) ≠ 0)
    (hd : coreClockFactor (coreRadius (beta t 0) (beta t 2)) (beta t 1) (beta t 3) ≠ 0) :
    HasDerivAt (fun s => coreClockProjection (beta s) (v s))
      (coreOriginalClockRate (beta t) •
        (coreAngleJacobian (projectiveCoreAngle (beta t)) (toCoreAngleState (beta t))).mulVec
          (coreClockProjection (beta t) (v t))) t := by
  have hr : (toCoreAngleState (beta t)) 0 ≠ 0 := ne_of_gt (coreRadius_pos hV)
  have hd' : coreAuxiliary (projectiveCoreAngle (beta t)) (toCoreAngleState (beta t)) 1 ≠ 0 := by
    rw [coreAuxiliary_projective_clockFactor hV]
    exact hd
  have hVnear : ∀ᶠ y : ProjectiveState in 𝓝 (beta t), 0 < y 2 :=
    (continuous_apply 2).continuousAt.eventually (isOpen_Ioi.mem_nhds hV)
  have hdnear := (contDiffAt_projectiveCoreClockFactor 1 hV).continuousAt.eventually_ne hd
  have hclock : (fun y => fderiv ℝ projectiveCoreAngle y (projectiveOriginalField y))
      =ᶠ[𝓝 (beta t)] coreOriginalClockRate := by
    filter_upwards [hVnear] with y hy
    exact projectiveCoreAngle_fderiv_field hy
  have hstate : (fun y => fderiv ℝ toCoreAngleState y (projectiveOriginalField y))
      =ᶠ[𝓝 (beta t)] (fun y => coreOriginalClockRate y •
        coreAngleField (projectiveCoreAngle y) (toCoreAngleState y)) := by
    filter_upwards [hVnear, hdnear] with y hy hdy
    exact toCoreAngleState_fderiv_field hy hdy
  have H := hasDerivAt_coordinate_clock_variation
    (contDiffAt_toCoreAngleState 2 hV) (contDiffAt_projectiveCoreAngle 2 hV)
    ((contDiffAt_projectiveOriginalField 1 hD).differentiableAt (by norm_num))
    ((contDiffAt_coreOriginalClockRate 1 hV hD).differentiableAt (by norm_num))
    ((contDiffAt_coreAngleField_joint 1 (projectiveCoreAngle (beta t)) hr hd').differentiableAt
      (by norm_num)) hbeta hv hclock hstate
  change HasDerivAt (fun s => coreClockProjection (beta s) (v s))
    (coreOriginalClockRate (beta t) •
      fderiv ℝ (coreAngleField (projectiveCoreAngle (beta t))) (toCoreAngleState (beta t))
        (coreClockProjection (beta t) (v t))) t at H
  rw [coreAngleField_fderiv _ hr hd'] at H
  exact H

/-- The projected actual initial-state derivative obeys the core variational equation. -/
theorem hasDerivAt_coreProjectedFlowVariation {y : ProjectiveState} {t₀ t : ℝ}
    (hD : 0 < projectiveStateDenom y) (ht : t ∈ normalizedMaxDomain (fromProjectiveState y) t₀)
    (hA : 0 < 1 + normalizedMaxCurve (fromProjectiveState y) t₀ t 0)
    (hV : 0 < projectiveOriginalFlow y t₀ t 2)
    (hd : coreClockFactor (coreRadius (projectiveOriginalFlow y t₀ t 0)
      (projectiveOriginalFlow y t₀ t 2)) (projectiveOriginalFlow y t₀ t 1)
        (projectiveOriginalFlow y t₀ t 3) ≠ 0) (w : ProjectiveState) :
    HasDerivAt (fun s => coreProjectedFlowVariation y t₀ s w)
      (coreOriginalClockRate (projectiveOriginalFlow y t₀ t) •
        (coreAngleJacobian (projectiveCoreAngle (projectiveOriginalFlow y t₀ t))
          (toCoreAngleState (projectiveOriginalFlow y t₀ t))).mulVec
            (coreProjectedFlowVariation y t₀ t w)) t := by
  have hc : stateConstraint (normalizedMaxCurve (fromProjectiveState y) t₀ t) = 1 :=
    (normalizedMaxCurve_constraint ht).trans (fromProjectiveState_constraint (ne_of_gt hD))
  exact hasDerivAt_coreClockProjection (hasDerivAt_projectiveOriginalFlow_time hD ht hA)
    (hasDerivAt_projectiveFlowDifferential_apply hD ht hA w) hV
    (ne_of_gt (toProjectiveState_denom_pos hA hc)) hd

theorem coreProjectedFlowVariation_initial {y : ProjectiveState}
    (hD : 0 < projectiveStateDenom y) (t₀ : ℝ) (w : ProjectiveState) :
    coreProjectedFlowVariation y t₀ t₀ w = coreClockProjection y w := by
  rw [coreProjectedFlowVariation, projectiveOriginalFlow_initial hD,
    projectiveFlowDifferential_initial hD, ContinuousLinearMap.id_apply]

end BianchiIX
