import BianchiIX.Dynamics.CoreSectionDifferential

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

/-- The incoming active-wall section in radius and transverse wall coordinates. -/
def coreRadiusEntry (Y : CoreAngleState) : ProjectiveState :=
  ![1 + Real.sqrt (Y 0 ^ 2 - 1), Y 1, 1, Y 2]

theorem coreRadius_coreRadiusEntry {Y : CoreAngleState} (hk : 1 < Y 0) :
    coreRadius (coreRadiusEntry Y 0) (coreRadiusEntry Y 2) = Y 0 := by
  have hk0 : 0 < Y 0 := lt_trans zero_lt_one hk
  have hsq := Real.sq_sqrt (by nlinarith only [hk] : 0 ≤ Y 0 ^ 2 - 1)
  have he : coreEnergy (coreRadiusEntry Y 0) (coreRadiusEntry Y 2) = Y 0 ^ 2 := by
    dsimp [coreRadiusEntry, coreEnergy]
    nlinarith only [hsq]
  rw [coreRadius, he, Real.sqrt_sq hk0.le]

theorem toCoreAngleState_coreRadiusEntry {Y : CoreAngleState} (hk : 1 < Y 0) :
    toCoreAngleState (coreRadiusEntry Y) = Y := by
  ext i
  fin_cases i
  · exact coreRadius_coreRadiusEntry hk
  · rfl
  · simp [toCoreAngleState, coreRadiusEntry]

theorem contDiffAt_coreRadiusEntry (n : WithTop ℕ∞) {Y : CoreAngleState} (hk : 1 < Y 0) :
    ContDiffAt ℝ n coreRadiusEntry Y := by
  have hs : Y 0 ^ 2 - 1 ≠ 0 := ne_of_gt (by nlinarith only [hk] : 0 < Y 0 ^ 2 - 1)
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i <;> dsimp [coreRadiusEntry] <;> fun_prop

theorem coreRadiusEntry_fderiv {Y : CoreAngleState} (hk : 1 < Y 0) (v : CoreAngleState) :
    fderiv ℝ coreRadiusEntry Y v = ![Y 0 / Real.sqrt (Y 0 ^ 2 - 1) * v 0, v 1, 0, v 2] := by
  have hs : Y 0 ^ 2 - 1 ≠ 0 := ne_of_gt (by nlinarith only [hk] : 0 < Y 0 ^ 2 - 1)
  have hd : HasDerivAt (fun s : ℝ => coreRadiusEntry (Y + s • v))
      ![Y 0 / Real.sqrt (Y 0 ^ 2 - 1) * v 0, v 1, 0, v 2] 0 := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · have H := (((((hasDerivAt_id (0 : ℝ)).mul_const (v 0)).const_add (Y 0)).pow 2).sub_const 1).sqrt
        (by simpa using hs)
      convert! H.const_add 1 using 1
      dsimp
      ring_nf
    · simpa [coreRadiusEntry] using ((hasDerivAt_id (0 : ℝ)).mul_const (v 1)).const_add (Y 1)
    · exact hasDerivAt_const 0 1
    · simpa [coreRadiusEntry] using ((hasDerivAt_id (0 : ℝ)).mul_const (v 2)).const_add (Y 2)
  have hl : HasDerivAt (fun s : ℝ => Y + s • v) v 0 := by
    convert! (hasDerivAt_const (0 : ℝ) Y).add ((hasDerivAt_id (0 : ℝ)).smul_const v) using 1
    simp
  have hf : HasFDerivAt coreRadiusEntry (fderiv ℝ coreRadiusEntry Y) (Y + (0 : ℝ) • v) := by
    simpa only [zero_smul, add_zero] using
      ((contDiffAt_coreRadiusEntry 1 hk).differentiableAt (by norm_num)).hasFDerivAt
  have H : HasDerivAt (fun s : ℝ => coreRadiusEntry (Y + s • v))
      (fderiv ℝ coreRadiusEntry Y v) 0 := by
    convert! hf.comp_hasDerivAt 0 hl using 1
  exact H.unique hd

theorem coreRadiusEntry_state_differential {Y : CoreAngleState} (hk : 1 < Y 0) :
    (fderiv ℝ toCoreAngleState (coreRadiusEntry Y)).comp (fderiv ℝ coreRadiusEntry Y) =
      ContinuousLinearMap.id ℝ CoreAngleState := by
  have hfrom := ((contDiffAt_coreRadiusEntry 1 hk).differentiableAt (by norm_num)).hasFDerivAt
  have hto := ((contDiffAt_toCoreAngleState 1 (show 0 < coreRadiusEntry Y 2 by change (0 : ℝ) < 1; norm_num)).differentiableAt
    (by norm_num)).hasFDerivAt
  have heq : (fun X => toCoreAngleState (coreRadiusEntry X)) =ᶠ[𝓝 Y] id := by
    filter_upwards [(continuous_apply 0).continuousAt.eventually (isOpen_Ioi.mem_nhds hk)] with X hX
    exact toCoreAngleState_coreRadiusEntry hX
  exact ((hto.comp Y hfrom).congr_of_eventuallyEq heq.symm).unique (hasFDerivAt_id Y)

theorem coreRadiusEntry_angle_differential {Y : CoreAngleState} (hk : 1 < Y 0) (v : CoreAngleState) :
    fderiv ℝ projectiveCoreAngle (coreRadiusEntry Y) (fderiv ℝ coreRadiusEntry Y v) =
      -v 0 / Real.sqrt (Y 0 ^ 2 - 1) := by
  have hk0 : Y 0 ≠ 0 := ne_of_gt (lt_trans zero_lt_one hk)
  rw [(coreCoordinate_fderiv (show 0 < coreRadiusEntry Y 2 by change (0 : ℝ) < 1; norm_num) _).2,
    coreRadius_coreRadiusEntry hk, coreRadiusEntry_fderiv hk]
  dsimp [coreRadiusEntry]
  field_simp
  ring

theorem coreRadiusEntry_angle_fderiv {Y : CoreAngleState} (hk : 1 < Y 0) (v : CoreAngleState) :
    fderiv ℝ (fun Z => projectiveCoreAngle (coreRadiusEntry Z)) Y v =
      -v 0 / Real.sqrt (Y 0 ^ 2 - 1) := by
  have hentry := ((contDiffAt_coreRadiusEntry 1 hk).differentiableAt (by norm_num)).hasFDerivAt
  have hangle := ((contDiffAt_projectiveCoreAngle 1
    (show 0 < coreRadiusEntry Y 2 by change (0 : ℝ) < 1; norm_num)).differentiableAt
      (by norm_num)).hasFDerivAt
  have H : HasFDerivAt (fun Z => projectiveCoreAngle (coreRadiusEntry Z))
      ((fderiv ℝ projectiveCoreAngle (coreRadiusEntry Y)).comp (fderiv ℝ coreRadiusEntry Y)) Y := by
    convert! hangle.comp Y hentry using 1
  rw [H.fderiv, ContinuousLinearMap.comp_apply]
  exact coreRadiusEntry_angle_differential hk v

/-- The moving incoming angle produces the exact initial datum for fixed-angle variation. -/
theorem coreRadiusEntry_projection {Y : CoreAngleState} (hk : 1 < Y 0) (v : CoreAngleState) :
    coreClockProjection (coreRadiusEntry Y) (fderiv ℝ coreRadiusEntry Y v) =
      v + (v 0 / Real.sqrt (Y 0 ^ 2 - 1)) • coreAngleField (projectiveCoreAngle (coreRadiusEntry Y)) Y := by
  have hstate := congrArg (fun L : CoreAngleState →L[ℝ] CoreAngleState => L v)
    (coreRadiusEntry_state_differential hk)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at hstate
  rw [coreClockProjection, hstate, coreRadiusEntry_angle_differential hk,
    toCoreAngleState_coreRadiusEntry hk, neg_div, neg_smul, sub_neg_eq_add]

theorem coreRadiusEntry_region {Y : CoreAngleState} (hk : 6 ≤ Y 0)
    (hu : 0 ≤ Y 1 ∧ Y 1 ≤ (1 / 10000) / Y 0)
    (hw : 0 ≤ Y 2 ∧ Y 2 ≤ (1 / 10000) / Y 0) :
    coreRegion (Y 0) (coreRadiusEntry Y) := by
  have hR := coreRadius_coreRadiusEntry (by linarith only [hk] : 1 < Y 0)
  have he := coreRadius_sq (coreRadiusEntry Y 0) (coreRadiusEntry Y 2)
  rw [hR] at he
  refine ⟨?_, le_rfl, hu, ?_⟩
  · rw [← he, sub_self, abs_zero]
    norm_num
  · simpa [coreRadiusEntry] using hw

end BianchiIX
