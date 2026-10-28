import BianchiIX.Dynamics.RestartRadialCutoff
import BianchiIX.Dynamics.ProjectiveState
import BianchiIX.Algebra.CoreAngle

noncomputable section

namespace BianchiIX

def restartProjectionDefect (p : RestartRadialState) : ℝ :=
  (p.2 0) ^ 2 + curvature p.1 (p.2 1) (p.2 2)

def restartProjectionHeight (p : RestartRadialState) : ℝ :=
  restartProjectionDefect p / (1 + Real.sqrt (1 - restartProjectionDefect p))

def restartProjectionPhase (p : RestartRadialState) : ℝ :=
  2 * restartProjectionHeight p /
    Real.sqrt ((Real.sqrt 3 * p.2 0 - restartProjectionHeight p) ^ 2 + 3 * (p.2 1) ^ 2)

theorem restartProjectionHeight_of_constraint {x : NormalizedState}
    (hc : stateConstraint x = 1) (hp : x 0 < 0) :
    restartProjectionHeight (x 2, ![x 1, x 3, x 4]) = 1 + x 0 := by
  have hd : restartProjectionDefect (x 2, ![x 1, x 3, x 4]) = 1 - (x 0) ^ 2 := by
    change (x 1) ^ 2 + curvature (x 2) (x 3) (x 4) = _
    dsimp only [stateConstraint, constraint, shearSq] at hc
    linarith only [hc]
  have hden : 1 - x 0 ≠ 0 := by linarith only [hp]
  rw [restartProjectionHeight, hd, show 1 - (1 - (x 0) ^ 2) = (x 0) ^ 2 by ring,
    Real.sqrt_sq_eq_abs, abs_of_neg hp]
  change (1 - x 0 ^ 2) / (1 - x 0) = 1 + x 0
  field_simp
  ring

/-- The regular expression is exactly the reciprocal core radius of the projective coordinates. -/
theorem restartProjectionPhase_eq_core {x : NormalizedState}
    (hc : stateConstraint x = 1) (hp : x 0 < 0) (hA : 0 < 1 + x 0) :
    restartProjectionPhase (x 2, ![x 1, x 3, x 4]) =
      2 / coreRadius (toProjectiveState x 0) (toProjectiveState x 2) := by
  have hsqrt : (Real.sqrt (3 : ℝ)) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hcore : coreRadius (toProjectiveState x 0) (toProjectiveState x 2) =
      Real.sqrt ((Real.sqrt 3 * x 1 - (1 + x 0)) ^ 2 + 3 * (x 3) ^ 2) / (1 + x 0) := by
    unfold coreRadius coreEnergy
    change Real.sqrt ((projectiveCoord (x 0) (x 1) - 1) ^ 2 +
      projectiveCoord (x 0) (x 3) ^ 2) = _
    have hid : (projectiveCoord (x 0) (x 1) - 1) ^ 2 + projectiveCoord (x 0) (x 3) ^ 2 =
        ((Real.sqrt 3 * x 1 - (1 + x 0)) ^ 2 + 3 * (x 3) ^ 2) / (1 + x 0) ^ 2 := by
      unfold projectiveCoord
      field_simp
      nlinarith only [hsqrt]
    rw [hid, Real.sqrt_div (by positivity), Real.sqrt_sq hA.le]
  rw [restartProjectionPhase, restartProjectionHeight_of_constraint hc hp, hcore]
  change 2 * (1 + x 0) / Real.sqrt ((Real.sqrt 3 * x 1 - (1 + x 0)) ^ 2 + 3 * x 3 ^ 2) = _
  rw [div_div_eq_mul_div]

end BianchiIX
