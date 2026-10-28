import BianchiIX.Dynamics.ConnectionLogFlowVariation
import BianchiIX.Dynamics.ConnectionReturnDifferential
import BianchiIX.Dynamics.ConnectionReturnValues

noncomputable section

namespace BianchiIX

theorem connectionLogTangent_arrival_correction {y v : ProjectiveState} (ζ : ℝ)
    (hm : 1 < -y 0) (hD : connectionClockRate y ≠ 0)
    (hu : y 1 ≠ 0) (hv : y 2 ≠ 0) (hw : y 3 ≠ 0) :
    connectionLogTangent y (connectionClockProjection y v 0) =
      connectionLogTangent y (connectionClockProjection y v ζ) - ζ • connectionLogCoordinateRates y := by
  have hid : connectionClockProjection y v 0 = connectionClockProjection y v ζ - ζ • connectionLogField y := by
    unfold connectionClockProjection
    module
  rw [← connectionLogCoordinates_fderiv hm hu hv hw, hid, map_sub, map_smul,
    connectionLogCoordinates_fderiv_field hm hD hu hv hw, connectionLogCoordinates_fderiv hm hu hv hw]

theorem connection_growing_projection_eq_clock {y v : ProjectiveState}
    (hD : connectionClockRate y ≠ 0) (hw : y 3 ≠ 0) :
    v - (v 3 / projectiveField y 3) • projectiveField y = connectionClockProjection y v 0 := by
  have hfield : projectiveField y 3 = connectionClockRate y * y 3 := rfl
  ext i
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, connectionClockProjection, sub_zero,
    connectionLogField, hfield]
  field_simp

theorem connectionInitialState_fderiv {p : ConnectionParameters}
    (hD : projectiveStateDenom (connectionEntry (p 0) (p 1) (p 2)) ≠ 0) (v : ConnectionParameters) :
    fderiv ℝ connectionInitialState p v =
      fderiv ℝ fromProjectiveState (connectionEntry (p 0) (p 1) (p 2)) ![-v 0, v 1, 0, v 2] := by
  have hline : HasDerivAt (fun s : ℝ => p + s • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add p
  have hentry : HasDerivAt (fun s : ℝ => connectionEntry ((p + s • v) 0) ((p + s • v) 1) ((p + s • v) 2))
      ![-v 0, v 1, 0, v 2] 0 := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · exact (hasDerivAt_pi.mp hline 0).neg
    · exact hasDerivAt_pi.mp hline 1
    · exact hasDerivAt_const _ _
    · exact hasDerivAt_pi.mp hline 2
  have hfrom := ((contDiffAt_fromProjectiveState 1 hD).differentiableAt (by norm_num)).hasFDerivAt
  have hfrom' : HasFDerivAt fromProjectiveState
      (fderiv ℝ fromProjectiveState (connectionEntry (p 0) (p 1) (p 2)))
      (connectionEntry ((p + (0 : ℝ) • v) 0) ((p + (0 : ℝ) • v) 1) ((p + (0 : ℝ) • v) 2)) := by simpa using hfrom
  have H := hfrom'.comp_hasDerivAt 0 hentry
  have hinit := ((contDiffAt_connectionInitialState 1 hD).differentiableAt (by norm_num)).hasFDerivAt
  have hinit' : HasFDerivAt connectionInitialState (fderiv ℝ connectionInitialState p) (p + (0 : ℝ) • v) := by simpa using hinit
  exact (hinit'.comp_hasDerivAt 0 hline).unique H

/-- The actual first-return derivative is the fixed-relative-clock derivative minus the moving endpoint term. -/
theorem connectionReturn_log_differential {p : ConnectionParameters} (hμ : 4 ≤ p 0)
    (hu : 0 < p 1 ∧ p 1 ≤ (1 / 10000) / p 0) (hw : 0 < p 2 ∧ p 2 ≤ 1 / 10000)
    (v : ConnectionParameters) :
    fderiv ℝ (connectionLogCoordinates ∘ connectionReturnState) p v =
      connectionLogFlowVariation (connectionEntry (p 0) (p 1) (p 2)) 0 (connectionReturnTime p) ![-v 0, v 1, 0, v 2] -
        (v 2 / p 2) • connectionLogCoordinateRates (connectionReturnState p) := by
  have hu' : 0 ≤ p 1 ∧ p 1 ≤ (1 / 10000) / p 0 := ⟨hu.1.le, hu.2⟩
  have hregular := connectionReturn_regular hμ hu' hw
  have hcontrol := connectionReturn_control hμ hu' hw
  have hregion := (hcontrol.2 (connectionReturnTime p) ⟨hcontrol.1.le, le_rfl⟩).2
  change connectionRegion (p 0) (connectionReturnState p) at hregion
  have hm : 1 < -connectionReturnState p 0 := by linarith only [hμ, (abs_le.mp hregion.1).1]
  have hD : connectionClockRate (connectionReturnState p) ≠ 0 := by
    have H := (connection_speed_bounds hμ hregion.1 hregion.2.1 hregion.2.2.1 hregion.2.2.2).1
    change p 0 / 2 ≤ connectionClockRate (connectionReturnState p) at H
    linarith only [H, hμ]
  have hpos := connectionReturn_wall_pos hμ hu' hw
  have hU := ne_of_gt (hpos.2 hu.1)
  have hV := ne_of_gt hpos.1
  have hW : connectionReturnState p 3 ≠ 0 := by rw [(connectionReturn_growing_component hμ hu' hw).1]; norm_num
  rw [fderiv_comp p ((contDiffAt_connectionLogCoordinates 1 hm hU hV hW).differentiableAt (by norm_num))
    (hregular.2.2.1.differentiableAt (by norm_num)), ContinuousLinearMap.comp_apply,
    connectionLogCoordinates_fderiv hm hU hV hW]
  have hd := (connectionReturn_differential hμ hu' hw v).2
  rw [connectionInitialState_fderiv (ne_of_gt (connection_entry_denom_pos hμ hu' hw))] at hd
  change fderiv ℝ connectionReturnState p v =
    projectiveFlowDifferential (connectionEntry (p 0) (p 1) (p 2)) 0 (connectionReturnTime p) ![-v 0, v 1, 0, v 2] -
      ((projectiveFlowDifferential (connectionEntry (p 0) (p 1) (p 2)) 0 (connectionReturnTime p) ![-v 0, v 1, 0, v 2]) 3 /
        projectiveField (connectionReturnState p) 3) • projectiveField (connectionReturnState p) at hd
  rw [hd, connection_growing_projection_eq_clock hD hW,
    connectionLogTangent_arrival_correction (v 2 / p 2) hm hD hU hV hW]
  rfl

end BianchiIX
