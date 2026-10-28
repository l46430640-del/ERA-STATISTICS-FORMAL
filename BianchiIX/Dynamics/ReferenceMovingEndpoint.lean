import BianchiIX.Dynamics.ReferenceRadiusResponse
import BianchiIX.Dynamics.ReferenceInteriorReturn
import BianchiIX.Dynamics.ProjectiveFlowSecondRegularity

noncomputable section

namespace BianchiIX

theorem hasDerivAt_fromCoreAngleState_strong (k z : ℝ) :
    HasDerivAt (fun u : ℝ => fromCoreAngleState z ![k, u, 0]) (Pi.single 1 1) 0 := by
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · simpa [fromCoreAngleState] using hasDerivAt_const (0 : ℝ) (1 - k * Real.tanh z)
  · change HasDerivAt (fun u : ℝ => u) 1 0
    exact hasDerivAt_id' 0
  · simpa [fromCoreAngleState] using hasDerivAt_const (0 : ℝ) (k / Real.cosh z)
  · simpa [fromCoreAngleState] using hasDerivAt_const (0 : ℝ) (0 : ℝ)

/-- Changing the initial angle on the boundary changes no core coordinate. -/
theorem referencePulse_angle_variation {k : ℝ} (hk : 0 < k) (z : ℝ) :
    let γ := fun a => referencePulse k (a / k)
    let w := (1 / k) • projectiveField (γ z)
    HasDerivAt γ w z ∧ fderiv ℝ toCoreAngleState (γ z) w = 0 ∧
      fderiv ℝ projectiveCoreAngle (γ z) w = 1 := by
  intro γ w
  have hγ : HasDerivAt γ w z := by
    have hlin : HasDerivAt (fun a : ℝ => a / k) (1 / k) z := (hasDerivAt_id z).div_const k
    convert! (hasDerivAt_referencePulse k (z / k)).hasFDerivAt.comp_hasDerivAt z hlin using 1
  have hY := ((contDiffAt_toCoreAngleState 1 (referencePulse_active_pos hk (z / k))).differentiableAt
    (by norm_num)).hasFDerivAt.comp_hasDerivAt z hγ
  have hz := ((contDiffAt_projectiveCoreAngle 1 (referencePulse_active_pos hk (z / k))).differentiableAt
    (by norm_num)).hasFDerivAt.comp_hasDerivAt z hγ
  have heY : (fun a => toCoreAngleState (γ a)) = fun _ => (![k, 0, 0] : CoreAngleState) := by
    ext a i
    exact congrFun (referencePulse_core_coordinates hk (a / k)).1 i
  have hez : (fun a => projectiveCoreAngle (γ a)) = id := by
    ext a
    rw [(referencePulse_core_coordinates hk (a / k)).2]
    exact mul_div_cancel₀ _ hk.ne'
  change HasDerivAt (fun a => toCoreAngleState (γ a)) _ z at hY
  change HasDerivAt (fun a => projectiveCoreAngle (γ a)) _ z at hz
  rw [heY] at hY
  rw [hez] at hz
  exact ⟨hγ, hY.unique (hasDerivAt_const z _), hz.unique (hasDerivAt_id z)⟩

/-- The moving endpoint contributes no radial term on the boundary reference orbit. -/
theorem referenceMovingEndpoint_radius_derivative {k : ℝ} (hk : 0 < k) (s t : ℝ)
    {τ : ProjectiveState → ℝ} (hτ : DifferentiableAt ℝ τ (referencePulse k s))
    (htime : τ (referencePulse k s) = referenceShiftClock k s t) (w : ProjectiveState) :
    let R := fun y : ProjectiveState => coreRadius (y 0) (y 2)
    fderiv ℝ (fun y => R (projectiveOriginalFlow y 0 (τ y))) (referencePulse k s) w =
      fderiv ℝ R (referencePulse k s) w +
        2 * referencePulse k s 2 * w 1 / k * (Real.exp (-(k ^ 2 / 2) * (t - s)) - 1) := by
  intro R
  have hdom : τ (referencePulse k s) ∈ normalizedMaxDomain (fromProjectiveState (referencePulse k s)) 0 := by
    rw [htime]
    exact (referenceShiftClock_normalized_orbit k s t).1
  have hA : 0 < 1 + normalizedMaxCurve (fromProjectiveState (referencePulse k s)) 0
      (τ (referencePulse k s)) 0 := by
    rw [htime]
    exact referenceShiftClock_chart_pos k s t
  have hout : projectiveOriginalFlow (referencePulse k s) 0 (τ (referencePulse k s)) = referencePulse k t := by
    rw [htime, referenceShiftClock_projective_orbit]
  have hF := (hasFDerivAt_projectiveOriginalFlow (referencePulse_denom_pos k s) hdom hA).comp
    (referencePulse k s) ((hasFDerivAt_id (referencePulse k s)).prodMk hτ.hasFDerivAt)
  have hR : HasFDerivAt R (fderiv ℝ R (referencePulse k t))
      (projectiveOriginalFlow (referencePulse k s) 0 (τ (referencePulse k s))) := by
    rw [hout]
    exact (hasFDerivAt_coreRadius_state (referencePulse_active_pos hk t)).differentiableAt.hasFDerivAt
  have H := hR.comp (referencePulse k s) hF
  change HasFDerivAt (fun y => R (projectiveOriginalFlow y 0 (τ y))) _ _ at H
  rw [H.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coprod_apply,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply,
    map_add, map_smul, hout]
  have hfield : fderiv ℝ R (referencePulse k t) (projectiveOriginalField (referencePulse k t)) = 0 := by
    rw [projectiveOriginalField, map_smul, referencePulse_radius_field hk, smul_zero]
  rw [hfield, smul_zero, add_zero, htime]
  exact referenceShiftedVariation_radius hk s t w

/-- The zero transverse velocities remove the moving-time correction from both wall rows. -/
theorem referenceMovingEndpoint_wall_derivative (k s t : ℝ)
    {τ : ProjectiveState → ℝ} (hτ : DifferentiableAt ℝ τ (referencePulse k s))
    (htime : τ (referencePulse k s) = referenceShiftClock k s t) (w : ProjectiveState) :
    fderiv ℝ (fun y => projectiveOriginalFlow y 0 (τ y) 1) (referencePulse k s) w =
        referenceTransverseMode k (k ^ 2 / 2) t / referenceTransverseMode k (k ^ 2 / 2) s * w 1 ∧
      fderiv ℝ (fun y => projectiveOriginalFlow y 0 (τ y) 3) (referencePulse k s) w =
        referenceTransverseMode k 2 t / referenceTransverseMode k 2 s * w 3 := by
  have hdom : τ (referencePulse k s) ∈ normalizedMaxDomain (fromProjectiveState (referencePulse k s)) 0 := by
    rw [htime]
    exact (referenceShiftClock_normalized_orbit k s t).1
  have hA : 0 < 1 + normalizedMaxCurve (fromProjectiveState (referencePulse k s)) 0
      (τ (referencePulse k s)) 0 := by
    rw [htime]
    exact referenceShiftClock_chart_pos k s t
  have hout : projectiveOriginalFlow (referencePulse k s) 0 (τ (referencePulse k s)) = referencePulse k t := by
    rw [htime, referenceShiftClock_projective_orbit]
  have hF := (hasFDerivAt_projectiveOriginalFlow (referencePulse_denom_pos k s) hdom hA).comp
    (referencePulse k s) ((hasFDerivAt_id (referencePulse k s)).prodMk hτ.hasFDerivAt)
  have hrow (i : Fin 4) :
      fderiv ℝ (fun y => projectiveOriginalFlow y 0 (τ y) i) (referencePulse k s) w =
        referenceShiftedVariation k s w t i +
          fderiv ℝ τ (referencePulse k s) w * projectiveOriginalField (referencePulse k t) i := by
    have H := hasFDerivAt_pi'.mp hF i
    change HasFDerivAt (fun y => projectiveOriginalFlow y 0 (τ y) i) _ _ at H
    rw [H.fderiv]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coprod_apply,
      ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.proj_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hout, htime]
    rfl
  have hfield : projectiveOriginalField (referencePulse k t) 1 = 0 ∧
      projectiveOriginalField (referencePulse k t) 3 = 0 := by
    simp [projectiveOriginalField, projectiveField, referencePulse, strongVelocity, weakVelocity]
  have H := referenceForcedVariation_transverse (I := Set.univ) convex_univ
    (fun r _ => hasDerivAt_referenceShiftedVariation k s r w) (Set.mem_univ s) (Set.mem_univ t)
  rw [referenceShiftedVariation_initial] at H
  rw [hrow 1, hrow 3, hfield.1, hfield.2]
  simpa only [mul_zero, zero_mul, add_zero, mul_comm] using H

theorem referenceTransverseMode_interior_ratio {k : ℝ} (hk : 1 < k) (s r : ℝ) :
    referenceTransverseMode k r (referenceHalfTime k) / referenceTransverseMode k r s =
      (k / Real.cosh (k * s)) * Real.exp (-r * (referenceHalfTime k - s)) := by
  have hk0 := (zero_lt_one.trans hk).ne'
  rw [show -r * (referenceHalfTime k - s) = -r * referenceHalfTime k - (-r * s) by ring,
    Real.exp_sub]
  dsimp only [referenceTransverseMode]
  rw [show k * referenceHalfTime k = Real.arcosh k by dsimp [referenceHalfTime]; field_simp,
    Real.cosh_arcosh hk.le]
  field_simp

end BianchiIX
