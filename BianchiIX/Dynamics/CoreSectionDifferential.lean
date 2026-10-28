import BianchiIX.Dynamics.CoreAngleEvents
import BianchiIX.Dynamics.CoreExitFactor
import BianchiIX.Dynamics.ReferenceEvents

noncomputable section

namespace BianchiIX

theorem coreCoordinate_fderiv {y : ProjectiveState} (hv : 0 < y 2) (v : ProjectiveState) :
    (fderiv ℝ toCoreAngleState y v) 0 =
        ((y 0 - 1) * v 0 + y 2 * v 2) / coreRadius (y 0) (y 2) ∧
      fderiv ℝ projectiveCoreAngle y v =
        ((y 0 - 1) * v 2 - y 2 * v 0) / (coreRadius (y 0) (y 2) * y 2) := by
  let beta : ℝ → ProjectiveState := fun s => y + s • v
  have hzero : beta 0 = y := by simp [beta]
  have hb : HasDerivAt beta v 0 := by
    convert! (hasDerivAt_const (0 : ℝ) y).add ((hasDerivAt_id (0 : ℝ)).smul_const v) using 1
    simp
  have hm := hasDerivAt_pi.mp hb 0
  have hV := hasDerivAt_pi.mp hb 2
  have hv' : 0 < beta 0 2 := by simpa only [hzero] using hv
  have hR := ((contDiffAt_toCoreAngleState 1 hv).differentiableAt (by norm_num)).hasFDerivAt
  have hz := ((contDiffAt_projectiveCoreAngle 1 hv).differentiableAt (by norm_num)).hasFDerivAt
  have hR' := hasDerivAt_pi.mp ((hzero.symm ▸ hR).comp_hasDerivAt 0 hb) 0
  have hz' := (hzero.symm ▸ hz).comp_hasDerivAt 0 hb
  constructor
  · simpa only [hzero] using hR'.unique (hasDerivAt_coreRadius hm hV hv')
  · simpa only [hzero] using hz'.unique (hasDerivAt_coreAngle hm hV hv')

theorem coreClockProjection_add_field {y : ProjectiveState} (hv : 0 < y 2)
    (hd : coreClockFactor (coreRadius (y 0) (y 2)) (y 1) (y 3) ≠ 0)
    (v : ProjectiveState) (a : ℝ) :
    coreClockProjection y (v + a • projectiveOriginalField y) = coreClockProjection y v := by
  simp only [coreClockProjection, map_add, map_smul, toCoreAngleState_fderiv_field hv hd,
    projectiveCoreAngle_fderiv_field hv]
  ext i
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Tangency to a constant active-wall section determines the moving angular endpoint. -/
theorem core_section_tangent_correction {y : ProjectiveState} (hv : 0 < y 2)
    (hden : -Real.tanh (projectiveCoreAngle y) +
      coreAngleField (projectiveCoreAngle y) (toCoreAngleState y) 0 / coreRadius (y 0) (y 2) ≠ 0)
    (v : ProjectiveState) (hv2 : v 2 = 0) :
    fderiv ℝ projectiveCoreAngle y v = -(coreClockProjection y v 0) /
        (coreRadius (y 0) (y 2) * (-Real.tanh (projectiveCoreAngle y) +
          coreAngleField (projectiveCoreAngle y) (toCoreAngleState y) 0 / coreRadius (y 0) (y 2))) ∧
      (fderiv ℝ toCoreAngleState y v) 0 = coreExitRadialFactor y * coreClockProjection y v 0 := by
  let r := coreRadius (y 0) (y 2)
  let c := -Real.tanh (projectiveCoreAngle y)
  let f := coreAngleField (projectiveCoreAngle y) (toCoreAngleState y) 0
  let q := coreClockProjection y v 0
  let dz := fderiv ℝ projectiveCoreAngle y v
  let dr := (fderiv ℝ toCoreAngleState y v) 0
  have hr : r ≠ 0 := ne_of_gt (coreRadius_pos hv)
  have hv0 := ne_of_gt hv
  have hcoord := coreCoordinate_fderiv hv v
  have htangent : dr + r * c * dz = 0 := by
    dsimp only [dr, dz, r, c]
    rw [hcoord.1, hcoord.2, hv2]
    change _ + coreRadius (y 0) (y 2) * (-Real.tanh (coreAngle (y 0) (y 2))) * _ = _
    rw [tanh_coreAngle hv]
    field_simp
    ring
  have hq : q = dr - dz * f := rfl
  have hden' : c + f / r ≠ 0 := hden
  have hz : dz = -q / (r * (c + f / r)) := by
    apply (eq_div_iff (mul_ne_zero hr hden')).mpr
    rw [mul_add, mul_div_cancel₀ f hr]
    nlinarith only [htangent, hq]
  refine ⟨hz, ?_⟩
  change dr = c / (c + f / r) * q
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff hden').mpr
  rw [mul_add]
  have hrel : r * c * dz = -dr := by linarith only [htangent]
  have hmul := congrArg (fun a : ℝ => a * f / r) hrel
  have he : r * c * dz * f / r = c * dz * f := by field_simp
  rw [he] at hmul
  linear_combination -c * hq + hmul

theorem coreWall_event_projection {x : NormalizedState} {t₀ t : ℝ}
    (hA : 1 + normalizedMaxCurve x t₀ t 0 ≠ 0)
    (hc : stateConstraint (normalizedMaxCurve x t₀ t) = 1)
    (hV : 0 < toProjectiveState (normalizedMaxCurve x t₀ t) 2)
    (hd : coreClockFactor
      (coreRadius (toProjectiveState (normalizedMaxCurve x t₀ t) 0)
        (toProjectiveState (normalizedMaxCurve x t₀ t) 2))
      (toProjectiveState (normalizedMaxCurve x t₀ t) 1)
      (toProjectiveState (normalizedMaxCurve x t₀ t) 3) ≠ 0)
    (hv : projectiveField (toProjectiveState (normalizedMaxCurve x t₀ t)) 2 ≠ 0)
    (v : NormalizedState) :
    let X := normalizedMaxCurve x t₀ t
    let y := toProjectiveState X
    let w := fderiv ℝ toProjectiveState X (normalizedEventDifferential projectiveActiveWall x t₀ t v)
    w 2 = 0 ∧ coreClockProjection y w =
      coreClockProjection y (fderiv ℝ toProjectiveState X (normalizedFlowDifferential x t₀ t v)) := by
  intro X y w
  have hproj := projective_event_differential hA hc hv v
  dsimp only at hproj
  constructor
  · change (fderiv ℝ toProjectiveState X (normalizedEventDifferential projectiveActiveWall x t₀ t v)) 2 = 0
    rw [hproj]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, div_mul_cancel₀ _ hv, sub_self]
  · have hpush : fderiv ℝ toProjectiveState X (normalizedField X) = projectiveOriginalField y := by
      have hs : 6 / projectiveStateDenom y = 1 + X 0 := projective_inverse_scale hA hc
      rw [toProjectiveState_fderiv_field hA hc, projectiveOriginalField, hs]
    have hw : w = fderiv ℝ toProjectiveState X (normalizedFlowDifferential x t₀ t v) +
        (normalizedEventTimeDifferential projectiveActiveWall x t₀ t v) • projectiveOriginalField y := by
      simp only [w, normalizedEventDifferential, add_apply,
        ContinuousLinearMap.smulRight_apply]
      rw [map_add, map_smul, hpush]
    rw [hw]
    exact coreClockProjection_add_field hV hd _ _

end BianchiIX
