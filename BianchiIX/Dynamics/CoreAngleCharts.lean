import BianchiIX.Dynamics.CoreFlowVariation

noncomputable section

namespace BianchiIX

open Filter
open scoped Topology

theorem contDiffAt_fromCoreAngleState (n : WithTop ℕ∞) (z : ℝ) {Y : CoreAngleState}
    (hr : Y 0 ≠ 0) : ContDiffAt ℝ n (fromCoreAngleState z) Y := by
  have hv : Y 0 / Real.cosh z ≠ 0 := div_ne_zero hr (ne_of_gt (Real.cosh_pos z))
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i <;> dsimp [fromCoreAngleState] <;> fun_prop

theorem fromCoreAngleState_active_pos (z : ℝ) {Y : CoreAngleState} (hr : 0 < Y 0) :
    0 < fromCoreAngleState z Y 2 := div_pos hr (Real.cosh_pos z)

theorem coreRadius_fromCoreAngleState (z : ℝ) {Y : CoreAngleState} (hr : 0 < Y 0) :
    coreRadius (fromCoreAngleState z Y 0) (fromCoreAngleState z Y 2) = Y 0 := by
  have hcosh := ne_of_gt (Real.cosh_pos z)
  have he : coreEnergy (fromCoreAngleState z Y 0) (fromCoreAngleState z Y 2) = Y 0 ^ 2 := by
    dsimp [coreEnergy, fromCoreAngleState]
    rw [Real.tanh_eq_sinh_div_cosh]
    field_simp
    nlinarith only [Real.cosh_sq_sub_sinh_sq z]
  rw [coreRadius, he, Real.sqrt_sq hr.le]

theorem toCoreAngleState_fromCoreAngleState (z : ℝ) {Y : CoreAngleState} (hr : 0 < Y 0) :
    toCoreAngleState (fromCoreAngleState z Y) = Y := by
  have hv := ne_of_gt (fromCoreAngleState_active_pos z hr)
  ext i
  fin_cases i
  · exact coreRadius_fromCoreAngleState z hr
  · rfl
  · change (Y 0 / Real.cosh z) * (Y 2 / (Y 0 / Real.cosh z)) = Y 2
    field_simp

theorem projectiveCoreAngle_fromCoreAngleState (z : ℝ) {Y : CoreAngleState} (hr : Y 0 ≠ 0) :
    projectiveCoreAngle (fromCoreAngleState z Y) = z := by
  have hcosh := ne_of_gt (Real.cosh_pos z)
  have he : (1 - (1 - Y 0 * Real.tanh z)) / (Y 0 / Real.cosh z) = Real.sinh z := by
    rw [Real.tanh_eq_sinh_div_cosh]
    field_simp
    ring
  change Real.arsinh ((1 - (1 - Y 0 * Real.tanh z)) / (Y 0 / Real.cosh z)) = z
  rw [he, Real.arsinh_sinh]

theorem coreAngle_chart_differential_inverse (z : ℝ) {Y : CoreAngleState} (hr : 0 < Y 0) :
    (fderiv ℝ toCoreAngleState (fromCoreAngleState z Y)).comp
        (fderiv ℝ (fromCoreAngleState z) Y) = ContinuousLinearMap.id ℝ CoreAngleState := by
  have hfrom := ((contDiffAt_fromCoreAngleState 1 z (ne_of_gt hr)).differentiableAt (by norm_num)).hasFDerivAt
  have hto := ((contDiffAt_toCoreAngleState 1 (fromCoreAngleState_active_pos z hr)).differentiableAt
    (by norm_num)).hasFDerivAt
  have heq : (fun X => toCoreAngleState (fromCoreAngleState z X)) =ᶠ[𝓝 Y] id := by
    filter_upwards [(continuous_apply 0).continuousAt.eventually (isOpen_Ioi.mem_nhds hr)] with X hX
    exact toCoreAngleState_fromCoreAngleState z hX
  exact ((hto.comp Y hfrom).congr_of_eventuallyEq heq.symm).unique (hasFDerivAt_id Y)

theorem coreAngle_chart_differential_clock (z : ℝ) {Y : CoreAngleState} (hr : 0 < Y 0) :
    (fderiv ℝ projectiveCoreAngle (fromCoreAngleState z Y)).comp
        (fderiv ℝ (fromCoreAngleState z) Y) = 0 := by
  have hfrom := ((contDiffAt_fromCoreAngleState 1 z (ne_of_gt hr)).differentiableAt (by norm_num)).hasFDerivAt
  have hangle := ((contDiffAt_projectiveCoreAngle 1 (fromCoreAngleState_active_pos z hr)).differentiableAt
    (by norm_num)).hasFDerivAt
  have heq : (fun X => projectiveCoreAngle (fromCoreAngleState z X)) =ᶠ[𝓝 Y] (fun _ => z) := by
    filter_upwards [(continuous_apply 0).continuousAt.eventually_ne (ne_of_gt hr)] with X hX
    exact projectiveCoreAngle_fromCoreAngleState z hX
  exact ((hangle.comp Y hfrom).congr_of_eventuallyEq heq.symm).unique (hasFDerivAt_const z Y)

theorem coreClockProjection_fromCoreAngleState (z : ℝ) {Y : CoreAngleState} (hr : 0 < Y 0)
    (v : CoreAngleState) :
    coreClockProjection (fromCoreAngleState z Y) (fderiv ℝ (fromCoreAngleState z) Y v) = v := by
  have hY := congrArg (fun L : CoreAngleState →L[ℝ] CoreAngleState => L v)
    (coreAngle_chart_differential_inverse z hr)
  have hz := congrArg (fun L : CoreAngleState →L[ℝ] ℝ => L v)
    (coreAngle_chart_differential_clock z hr)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, zero_apply] at hY hz
  rw [coreClockProjection, hY, hz, zero_smul, sub_zero]

end BianchiIX
