import BianchiIX.Dynamics.ConnectionArrivalVariation
import BianchiIX.Analysis.ConnectionPhaseEndpointFactor

noncomputable section

namespace BianchiIX

theorem connectionExitPhase_tangent {y v : ProjectiveState} (hw : y 3 = 1)
    (hf : matchingPhaseSlope (-y 0) (y 2) 1 ≠ 0) (hvw : v 3 = 0) :
    ((-y 0 - 1) / phaseNorm (-y 0 - 1) 1) * (-v 0) =
      connectionExitPhaseFactor (-y 0) (y 2) * (connectionLogTangent y v 0 -
        ((y 2) ^ 2 / phaseNorm (-y 0 + 1) (y 2)) * connectionLogTangent y v 2) := by
  simp [connectionExitPhaseFactor, connectionLogTangent, hw, hvw]
  field_simp
  ring

/-- The physical phase derivative follows directly from the matching phase and one weak log amplitude. -/
theorem connectionReturnPhaseError_differential {p : ConnectionParameters} (hμ : 4 ≤ p 0)
    (hu : 0 < p 1 ∧ p 1 ≤ (1 / 10000) / p 0) (hw : 0 < p 2 ∧ p 2 ≤ 1 / 10000)
    (v : ConnectionParameters) :
    let y := connectionReturnState p
    let J := fderiv ℝ (connectionLogCoordinates ∘ connectionReturnState) p v
    fderiv ℝ connectionReturnPhaseError p v =
      connectionExitPhaseFactor (-y 0) (y 2) *
        (J 0 - ((y 2) ^ 2 / phaseNorm (-y 0 + 1) (y 2)) * J 2) -
      ((p 0 + 1) / phaseNorm (p 0 + 1) 1) * v 0 := by
  intro y J
  let ξ := fderiv ℝ connectionReturnState p v
  have hu' : 0 ≤ p 1 ∧ p 1 ≤ (1 / 10000) / p 0 := ⟨hu.1.le, hu.2⟩
  have hc := connectionReturn_control hμ hu' hw
  have hr := (hc.2 (connectionReturnTime p) ⟨hc.1.le, le_rfl⟩).2
  change connectionRegion (p 0) y at hr
  have hm : 1 < -y 0 := by linarith only [hμ, (abs_le.mp hr.1).1]
  have hpos := connectionReturn_wall_pos hμ hu' hw
  have hU : y 1 ≠ 0 := ne_of_gt (hpos.2 hu.1)
  have hV : y 2 ≠ 0 := ne_of_gt hpos.1
  have hW : y 3 = 1 := (connectionReturn_growing_component hμ hu' hw).1
  have hξW : ξ 3 = 0 := (connectionReturn_growing_component hμ hu' hw).2 v
  have hf : matchingPhaseSlope (-y 0) (y 2) 1 ≠ 0 := by
    have H := (matchingPhase_slope_bounds hμ hr.1 hr.2.2.1 ⟨by norm_num, le_rfl⟩).1
    linarith only [H]
  have hstate := ((connectionReturn_regular hμ hu' hw).2.2.1.differentiableAt (by norm_num)).hasFDerivAt
  have hJ : J = connectionLogTangent y ξ := by
    dsimp [J]
    rw [fderiv_comp p ((contDiffAt_connectionLogCoordinates 1 hm hU hV (by rw [hW]; norm_num)).differentiableAt (by norm_num))
      hstate.differentiableAt, ContinuousLinearMap.comp_apply, connectionLogCoordinates_fderiv hm hU hV (by rw [hW]; norm_num)]
  have hline : HasDerivAt (fun s : ℝ => p + s • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add p
  have hstate' : HasFDerivAt connectionReturnState (fderiv ℝ connectionReturnState p) (p + (0 : ℝ) • v) := by
    simpa using hstate
  have hpath := hstate'.comp_hasDerivAt 0 hline
  have hout := hasDerivAt_phaseNorm ((hasDerivAt_pi.mp hpath 0).neg.sub_const 1) (hasDerivAt_const 0 (1 : ℝ))
    (by simpa [Function.comp_def, y] using (show 0 < -y 0 - 1 by linarith only [hm]))
  have hin := hasDerivAt_phaseNorm ((hasDerivAt_pi.mp hline 0).add_const 1) (hasDerivAt_const 0 (1 : ℝ))
    (by simpa using (show 0 < p 0 + 1 by linarith only [hμ]))
  have hdelta : HasFDerivAt connectionReturnPhaseError (fderiv ℝ connectionReturnPhaseError p) (p + (0 : ℝ) • v) := by
    simpa using ((contDiffAt_connectionReturnPhaseError hμ hu' hw).differentiableAt (by norm_num)).hasFDerivAt
  have hraw : fderiv ℝ connectionReturnPhaseError p v =
      ((-y 0 - 1) / phaseNorm (-y 0 - 1) 1) * (-ξ 0) -
      ((p 0 + 1) / phaseNorm (p 0 + 1) 1) * v 0 := by
    have hdline : HasDerivAt (fun s : ℝ => connectionReturnPhaseError (p + s • v))
        (fderiv ℝ connectionReturnPhaseError p v) 0 :=
      HasFDerivAt.comp_hasDerivAt (l := connectionReturnPhaseError)
        (l' := fderiv ℝ connectionReturnPhaseError p) (f := fun s : ℝ => p + s • v) 0 hdelta hline
    have hcalc : HasDerivAt (fun s : ℝ => connectionReturnPhaseError (p + s • v))
        (((-y 0 - 1) / phaseNorm (-y 0 - 1) 1) * (-ξ 0) -
          ((p 0 + 1) / phaseNorm (p 0 + 1) 1) * v 0) 0 := by
      simpa [connectionReturnPhaseError, Function.comp_def, y, ξ, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
        using (hout.sub hin).add_const 2
    exact hdline.unique hcalc
  rw [hraw, hJ, connectionExitPhase_tangent hW hf hξW]

end BianchiIX
