import BianchiIX.Dynamics.Normalized
import BianchiIX.Algebra.Coordinates

noncomputable section

namespace BianchiIX

abbrev ProjectiveState := Fin 4 → ℝ

def toProjectiveState (x : NormalizedState) : ProjectiveState :=
  ![projectiveCoord (x 0) (x 1), projectiveCoord (x 0) (x 2),
    projectiveCoord (x 0) (x 3), projectiveCoord (x 0) (x 4)]

def projectiveStateDenom (y : ProjectiveState) : ℝ :=
  projectiveDenom (y 0) (y 1) (y 2) (y 3)

def fromProjectiveState (y : ProjectiveState) : NormalizedState :=
  let A := 6 / projectiveStateDenom y
  ![A - 1, A * y 0 / Real.sqrt 3, A * y 1 / Real.sqrt 3,
    A * y 2 / Real.sqrt 3, A * y 3 / Real.sqrt 3]

def projectiveField (y : ProjectiveState) : ProjectiveState :=
  ![phaseVelocity (y 0) (y 1) (y 2) (y 3),
    strongVelocity (y 0) (y 1) (y 2) (y 3),
    activeVelocity (y 0) (y 1) (y 2) (y 3),
    weakVelocity (y 0) (y 1) (y 2) (y 3)]

theorem continuous_projectiveStateDenom : Continuous projectiveStateDenom := by
  unfold projectiveStateDenom projectiveDenom curvature
  fun_prop

theorem fromProjectiveState_toProjectiveState {x : NormalizedState}
    (hA : 1 + x 0 ≠ 0) (hc : stateConstraint x = 1) :
    fromProjectiveState (toProjectiveState x) = x := by
  have hscale : 6 / projectiveStateDenom (toProjectiveState x) = 1 + x 0 :=
    projective_inverse_scale hA hc
  unfold fromProjectiveState
  rw [hscale]
  ext i
  fin_cases i
  · change 1 + x 0 - 1 = x 0
    ring
  all_goals exact projective_inverse_coord hA

theorem toProjectiveState_fromProjectiveState {y : ProjectiveState}
    (hD : projectiveStateDenom y ≠ 0) :
    toProjectiveState (fromProjectiveState y) = y := by
  have hA : 6 / projectiveStateDenom y ≠ 0 := div_ne_zero (by norm_num) hD
  ext i
  fin_cases i <;> exact projective_forward_coord hA

theorem fromProjectiveState_constraint {y : ProjectiveState}
    (hD : projectiveStateDenom y ≠ 0) : stateConstraint (fromProjectiveState y) = 1 :=
  constraint_of_inverse_projective hD

theorem toProjectiveState_denom_pos {x : NormalizedState}
    (hA : 0 < 1 + x 0) (hc : stateConstraint x = 1) :
    0 < projectiveStateDenom (toProjectiveState x) :=
  projectiveDenom_positive hA hc

theorem fromProjectiveState_clock_pos {y : ProjectiveState}
    (hD : 0 < projectiveStateDenom y) : 0 < 1 + fromProjectiveState y 0 := by
  change 0 < 1 + (6 / projectiveStateDenom y - 1)
  linarith [div_pos (show (0 : ℝ) < 6 by norm_num) hD]

theorem toProjectiveState_positive {x : NormalizedState}
    (hA : 0 < 1 + x 0) (hx : positiveWalls x) :
    0 < toProjectiveState x 1 ∧ 0 < toProjectiveState x 2 ∧ 0 < toProjectiveState x 3 := by
  have hr : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  exact ⟨div_pos (mul_pos hr hx.1) hA, div_pos (mul_pos hr hx.2.1) hA,
    div_pos (mul_pos hr hx.2.2) hA⟩

theorem fromProjectiveState_positive {y : ProjectiveState}
    (hD : 0 < projectiveStateDenom y) (hy : 0 < y 1 ∧ 0 < y 2 ∧ 0 < y 3) :
    positiveWalls (fromProjectiveState y) := by
  have hA : 0 < 6 / projectiveStateDenom y := div_pos (by norm_num) hD
  have hr : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  exact ⟨div_pos (mul_pos hA hy.1) hr, div_pos (mul_pos hA hy.2.1) hr,
    div_pos (mul_pos hA hy.2.2) hr⟩

theorem hasDerivAt_reparametrized_projectiveState {α : ℝ → NormalizedState}
    {clock : ℝ → ℝ} {τ : ℝ}
    (hα : HasDerivAt α (normalizedField (α (clock τ))) (clock τ))
    (hA : 0 < 1 + α (clock τ) 0) (hc : stateConstraint (α (clock τ)) = 1)
    (hclock : HasDerivAt clock (1 / (1 + α (clock τ) 0)) τ) :
    HasDerivAt (fun u => toProjectiveState (α (clock u)))
      (projectiveField (toProjectiveState (α (clock τ)))) τ := by
  obtain ⟨hp, hs, ha, hb, hw⟩ := hasDerivAt_normalized_components hα
  obtain ⟨hm, hu, hv, hw⟩ :=
    hasDerivAt_reparametrized_projective_flow
      (p := fun t => α t 0) (s := fun t => α t 1) (a := fun t => α t 2)
      (b := fun t => α t 3) (c := fun t => α t 4) hp hs ha hb hw hA hc hclock
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · exact hm
  · exact hu
  · exact hv
  · exact hw

end BianchiIX
