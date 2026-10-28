import BianchiIX.Dynamics.Normalized
import BianchiIX.Algebra.RestartTransport
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

noncomputable section

namespace BianchiIX

def restartCurvatureDifference (x : NormalizedState) : ℝ :=
  (x 3 - x 4) ^ 2 - 2 * x 2 * (x 3 + x 4)

def restartRootDifference (x : NormalizedState) : ℝ := -x 0 - restartReferenceRoot (x 2)

def restartStrongRateDifference (x : NormalizedState) : ℝ :=
  restartCurvatureDifference x - 2 * restartRootDifference x

theorem curvature_restart_decomposition (x : NormalizedState) :
    curvature (x 2) (x 3) (x 4) = x 2 ^ 2 + restartCurvatureDifference x := by
  dsimp only [curvature, restartCurvatureDifference]
  ring

theorem restart_negative_branch_root {x : NormalizedState}
    (hc : stateConstraint x = 1) (hp : x 0 < 0) :
    -x 0 = Real.sqrt (1 - x 1 ^ 2 - curvature (x 2) (x 3) (x 4)) := by
  have hr : 1 - x 1 ^ 2 - curvature (x 2) (x 3) (x 4) = x 0 ^ 2 := by
    dsimp only [stateConstraint, constraint, shearSq] at hc
    linarith only [hc]
  rw [hr, Real.sqrt_sq_eq_abs, abs_of_neg hp]

/-- The root difference is quadratic in the center variables and retains its strong-wall factor. -/
theorem restartRootDifference_rationalized {x : NormalizedState}
    (hc : stateConstraint x = 1) (hp : x 0 < 0) (hn : x 2 ^ 2 < 1) :
    restartRootDifference x =
      -(x 1 ^ 2 + restartCurvatureDifference x) / (-x 0 + restartReferenceRoot (x 2)) := by
  have hz := restartReferenceRoot_pos hn
  have hd : -x 0 + restartReferenceRoot (x 2) ≠ 0 := by linarith only [hp, hz]
  apply (eq_div_iff hd).mpr
  dsimp only [stateConstraint, constraint, shearSq] at hc
  rw [curvature_restart_decomposition] at hc
  dsimp only [restartRootDifference]
  nlinarith only [hc, restartReferenceRoot_sq hn.le]

/-- Exact original-time equations for the strong wall, shear, and weak-wall difference. -/
theorem hasDerivAt_restart_components {x : ℝ → NormalizedState} {t : ℝ}
    (hx : HasDerivAt x (normalizedField (x t)) t) (hc : stateConstraint (x t) = 1) :
    HasDerivAt (fun r => x r 2)
      (x t 2 * (restartReferenceStrongRate (x t 2) + restartStrongRateDifference (x t))) t ∧
    HasDerivAt (fun r => x r 1)
      (x t 2 ^ 2 * x t 1 + Real.sqrt 3 * x t 2 * (x t 3 - x t 4) +
        (restartCurvatureDifference (x t) * x t 1 - Real.sqrt 3 * (x t 3 + x t 4) * (x t 3 - x t 4))) t ∧
    HasDerivAt (fun r => x r 3 - x r 4)
      (restartReferenceWallRate (x t 2) * (x t 3 - x t 4) +
        (restartCurvatureDifference (x t) + restartRootDifference (x t)) * (x t 3 - x t 4) +
        Real.sqrt 3 * (x t 3 + x t 4) * x t 1) t := by
  obtain ⟨_, hs, hn, ha, hb⟩ := hasDerivAt_normalized_components hx
  have hq : shearSq (x t 0) (x t 1) = 1 - curvature (x t 2) (x t 3) (x t 4) := by
    dsimp only [stateConstraint, constraint] at hc
    linarith only [hc]
  refine ⟨hn.congr_deriv ?_, hs.congr_deriv ?_, (ha.sub hb).congr_deriv ?_⟩
  · dsimp only [rateOne, restartReferenceStrongRate, restartStrongRateDifference, restartRootDifference]
    rw [hq, curvature_restart_decomposition]
    ring
  · dsimp only [shearMinus, curvature, restartCurvatureDifference]
    ring
  · dsimp only [rateTwo, rateThree, restartReferenceWallRate, restartRootDifference]
    rw [hq, curvature_restart_decomposition]
    ring

theorem hasDerivAt_restart_strong_log {x : ℝ → NormalizedState} {t : ℝ}
    (hx : HasDerivAt x (normalizedField (x t)) t) (hc : stateConstraint (x t) = 1)
    (hn : 0 < x t 2) :
    HasDerivAt (fun r => Real.log (x r 2))
      (restartReferenceStrongRate (x t 2) + restartStrongRateDifference (x t)) t := by
  simpa only [mul_div_cancel_left₀ _ hn.ne'] using ((hasDerivAt_restart_components hx hc).1).log hn.ne'

end BianchiIX
