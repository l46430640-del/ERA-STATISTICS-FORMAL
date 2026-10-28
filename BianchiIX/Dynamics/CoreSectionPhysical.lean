import BianchiIX.Dynamics.TaubAvoidance
import BianchiIX.Dynamics.CoreDownwardIdentification

noncomputable section

namespace BianchiIX

theorem unit_active_wall_clock_ne_zero {x : NormalizedState} (hv : toProjectiveState x 2 = 1) :
    1 + x 0 ≠ 0 := by
  intro hzero
  change projectiveCoord (x 0) (x 3) = 1 at hv
  simp only [projectiveCoord, hzero, div_zero] at hv
  norm_num at hv

theorem unit_active_wall_denom_pos {y : ProjectiveState} (hv : y 2 = 1)
    (hu : 0 ≤ y 1 ∧ y 1 ≤ 1 / 4) (hw : 0 ≤ y 3 ∧ y 3 ≤ 1 / 4) :
    0 < projectiveStateDenom y := by
  have hp : y 1 * (1 + y 3) ≤ 5 / 16 := by
    have H := mul_le_mul hu.2 (by linarith only [hw.2] : 1 + y 3 ≤ 5 / 4)
      (by linarith only [hw.1] : 0 ≤ 1 + y 3) (by norm_num : (0 : ℝ) ≤ 1 / 4)
    norm_num at H
    exact H
  rw [projectiveStateDenom, projectiveDenom_eq, hv]
  nlinarith only [hp, sq_nonneg (y 0), sq_nonneg (y 1), sq_nonneg (1 - y 3)]

/-- A small-wall upward unit crossing has the positive radius branch and reconstructs the physical state. -/
theorem upward_core_normalized_reconstruction {x : NormalizedState}
    (hc : stateConstraint x = 1) (hv : toProjectiveState x 2 = 1)
    (hu : 0 ≤ toProjectiveState x 1 ∧ toProjectiveState x 1 ≤ 1 / 4)
    (hw : 0 ≤ toProjectiveState x 3 ∧ toProjectiveState x 3 ≤ 1 / 4)
    (htrans : 0 < fderiv ℝ projectiveActiveWall x (normalizedField x)) :
    let y := toProjectiveState x
    coreRadiusEntry ![coreRadius (y 0) (y 2), y 1, y 3] = y ∧
      fromProjectiveState (coreRadiusEntry ![coreRadius (y 0) (y 2), y 1, y 3]) = x := by
  intro y
  have hA := unit_active_wall_clock_ne_zero hv
  have hx := fromProjectiveState_toProjectiveState hA hc
  have hclock : 0 < 1 + x 0 := by
    simpa only [hx] using fromProjectiveState_clock_pos (unit_active_wall_denom_pos hv hu hw)
  rw [projectiveActiveWall_fderiv_field hA hc] at htrans
  have hvel : 0 < projectiveField y 2 := by
    by_contra! hn
    exact (not_le_of_gt htrans) (mul_nonpos_of_nonneg_of_nonpos hclock.le hn)
  change 0 < activeVelocity (y 0) (y 1) (y 2) (y 3) at hvel
  change y 2 = 1 at hv
  rw [activeVelocity, hv, mul_one] at hvel
  have hcoupling : 0 ≤ coupling (y 1) 1 (y 3) :=
    mul_nonneg hu.1 (by linarith only [hu.2, hw.1])
  have hm : 1 ≤ y 0 := by linarith only [hvel, hcoupling]
  have hcoords : toCoreAngleState y = ![coreRadius (y 0) (y 2), y 1, y 3] := by
    simp only [toCoreAngleState, hv, one_mul]
  have heq := coreRadiusEntry_of_upward_section hm hv
  rw [hcoords] at heq
  exact ⟨heq, (congrArg fromProjectiveState heq).trans hx⟩

theorem coreReturn_normalized_endpoint {Y : CoreAngleState} (H : coreRadiusReturnValid Y)
    (hchart : coreTailEntry (coreReturnState coreRadiusReturnTime Y) =
      projectiveOriginalFlow (coreRadiusEntry Y) 0 (coreRadiusReturnTime Y)) :
    fromProjectiveState (coreTailEntry (coreReturnState coreRadiusReturnTime Y)) =
      normalizedMaxCurve (fromProjectiveState (coreRadiusEntry Y)) 0 (coreRadiusReturnTime Y) := by
  have hA := (H.2.1 (coreRadiusReturnTime Y) ⟨H.1.1.1.le, le_rfl⟩).2
  rw [hchart]
  exact fromProjectiveState_toProjectiveState hA.ne'
    ((normalizedMaxCurve_constraint H.1.1.2.1).trans
      (fromProjectiveState_constraint (coreRadiusReturnValid_denom_pos H).ne'))

theorem normalizedTaubAvoidance.coreReturn {ε : ℝ} {Y : CoreAngleState}
    (Ha : normalizedTaubAvoidance ε (fromProjectiveState (coreRadiusEntry Y)))
    (H : coreRadiusReturnValid Y)
    (hchart : coreTailEntry (coreReturnState coreRadiusReturnTime Y) =
      projectiveOriginalFlow (coreRadiusEntry Y) 0 (coreRadiusReturnTime Y)) :
    normalizedTaubAvoidance ε (fromProjectiveState (coreTailEntry (coreReturnState coreRadiusReturnTime Y))) := by
  rw [coreReturn_normalized_endpoint H hchart]
  exact Ha.forward H.1.1.1.le H.1.1.2.1

end BianchiIX
