import BianchiIX.Algebra.AxisCycle
import BianchiIX.Dynamics.ProjectiveState
import BianchiIX.Dynamics.AxisSymmetry

noncomputable section

namespace BianchiIX

def projectiveCycleDenom (y : ProjectiveState) : ℝ := axisCycleDenom (y 0) (y 1) (y 2) (y 3)

def projectiveCycle (y : ProjectiveState) : ProjectiveState :=
  ![1 - 4 * (y 0 + 1) / projectiveCycleDenom y, 4 * y 2 / projectiveCycleDenom y,
    4 * y 3 / projectiveCycleDenom y, 4 * y 1 / projectiveCycleDenom y]

theorem contDiff_projectiveCycleDenom (n : WithTop ℕ∞) : ContDiff ℝ n projectiveCycleDenom := by
  unfold projectiveCycleDenom axisCycleDenom curvature
  fun_prop

theorem contDiffAt_projectiveCycle (n : WithTop ℕ∞) {y : ProjectiveState}
    (hH : projectiveCycleDenom y ≠ 0) : ContDiffAt ℝ n projectiveCycle y := by
  have hD := (contDiff_projectiveCycleDenom n).contDiffAt (x := y)
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i
  · change ContDiffAt ℝ n (fun z : ProjectiveState => 1 - 4 * (z 0 + 1) / projectiveCycleDenom z) y
    fun_prop (disch := assumption)
  all_goals
    change ContDiffAt ℝ n (fun z : ProjectiveState => 4 * z _ / projectiveCycleDenom z) y
    fun_prop (disch := assumption)

theorem projectiveCycleDenom_eq (y : ProjectiveState) :
    projectiveCycleDenom y = projectiveStateDenom y + 2 * y 0 - 2 :=
  axisCycleDenom_projective _ _ _ _

theorem axisCycle_inverse_clock {y : ProjectiveState} (hD : projectiveStateDenom y ≠ 0) :
    1 + axisCycle (fromProjectiveState y) 0 =
      (6 / projectiveStateDenom y) * projectiveCycleDenom y / 4 := by
  have hr : Real.sqrt 3 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)).ne'
  rw [projectiveCycleDenom_eq]
  dsimp only [axisCycle, fromProjectiveState, Matrix.cons_val_zero, Matrix.cons_val_one]
  field_simp
  ring

theorem toProjectiveState_axisCycle_inverse {y : ProjectiveState}
    (hD : projectiveStateDenom y ≠ 0) (hH : projectiveCycleDenom y ≠ 0) :
    toProjectiveState (axisCycle (fromProjectiveState y)) = projectiveCycle y := by
  have hr : Real.sqrt 3 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)).ne'
  have hr2 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have Hclock := axisCycle_inverse_clock hD
  have HH := projectiveCycleDenom_eq y
  ext i
  fin_cases i <;> change Real.sqrt 3 * axisCycle (fromProjectiveState y) _ /
    (1 + axisCycle (fromProjectiveState y) 0) = _ <;> rw [Hclock]
  · change Real.sqrt 3 * ((-Real.sqrt 3 * (6 / projectiveStateDenom y - 1) -
        6 / projectiveStateDenom y * y 0 / Real.sqrt 3) / 2) /
        (6 / projectiveStateDenom y * projectiveCycleDenom y / 4) =
      1 - 4 * (y 0 + 1) / projectiveCycleDenom y
    field_simp
    ring_nf
    rw [hr2]
    nlinarith only [HH]
  all_goals
    dsimp [axisCycle, fromProjectiveState, projectiveCycle]
    field_simp

theorem axisCycle_projective_clock {x : NormalizedState} (hA : 1 + x 0 ≠ 0) (hc : stateConstraint x = 1) :
    1 + axisCycle x 0 = (1 + x 0) * projectiveCycleDenom (toProjectiveState x) / 4 := by
  have hD : projectiveStateDenom (toProjectiveState x) ≠ 0 := by
    have HD : projectiveStateDenom (toProjectiveState x) = 6 / (1 + x 0) := projectiveDenom_of_constraint hA hc
    rw [HD]
    exact div_ne_zero (by norm_num) hA
  have H := axisCycle_inverse_clock hD
  rw [fromProjectiveState_toProjectiveState hA hc] at H
  have Hscale : 6 / projectiveStateDenom (toProjectiveState x) = 1 + x 0 := projective_inverse_scale hA hc
  rwa [Hscale] at H

theorem toProjectiveState_axisCycle {x : NormalizedState} (hA : 1 + x 0 ≠ 0) (hc : stateConstraint x = 1)
    (hH : projectiveCycleDenom (toProjectiveState x) ≠ 0) :
    toProjectiveState (axisCycle x) = projectiveCycle (toProjectiveState x) := by
  have hD : projectiveStateDenom (toProjectiveState x) ≠ 0 := by
    have HD : projectiveStateDenom (toProjectiveState x) = 6 / (1 + x 0) := projectiveDenom_of_constraint hA hc
    rw [HD]
    exact div_ne_zero (by norm_num) hA
  have H := toProjectiveState_axisCycle_inverse hD hH
  rwa [fromProjectiveState_toProjectiveState hA hc] at H

theorem axisCycle_projective_clock_pos {x : NormalizedState} (hA : 0 < 1 + x 0) (hc : stateConstraint x = 1)
    (hH : 0 < projectiveCycleDenom (toProjectiveState x)) :
    0 < 1 + axisCycle x 0 ∧ (1 + axisCycle x 0) / (1 + x 0) = projectiveCycleDenom (toProjectiveState x) / 4 := by
  rw [axisCycle_projective_clock hA.ne' hc]
  exact ⟨div_pos (mul_pos hA hH) (by norm_num), by field_simp⟩

end BianchiIX
