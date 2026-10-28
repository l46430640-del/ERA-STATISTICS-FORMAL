import BianchiIX.Dynamics.AxisSymmetry
import BianchiIX.Dynamics.ProjectiveFlowVariation
import BianchiIX.Dynamics.ConstrainedComplete

noncomputable section

namespace BianchiIX

def projectiveReflection (y : ProjectiveState) : ProjectiveState := ![-y 0, y 1, y 3, y 2]

theorem projectiveReflection_twice (y : ProjectiveState) : projectiveReflection (projectiveReflection y) = y := by
  ext i
  fin_cases i <;> simp [projectiveReflection]

theorem projectiveReflection_denom (y : ProjectiveState) :
    projectiveStateDenom (projectiveReflection y) = projectiveStateDenom y := by
  dsimp [projectiveStateDenom, projectiveDenom, projectiveReflection, curvature]
  ring

theorem toProjectiveState_axisSwap (x : NormalizedState) :
    toProjectiveState (axisSwap x) = projectiveReflection (toProjectiveState x) := by
  ext i
  fin_cases i <;> dsimp [toProjectiveState, axisSwap, projectiveReflection, projectiveCoord]
  all_goals ring

theorem fromProjectiveState_reflection (y : ProjectiveState) :
    fromProjectiveState (projectiveReflection y) = axisSwap (fromProjectiveState y) := by
  simp only [fromProjectiveState, projectiveReflection_denom]
  ext i
  fin_cases i <;> dsimp [projectiveReflection, axisSwap]
  all_goals ring

theorem projectiveOriginalFlow_reflection {y : ProjectiveState} {t₀ t : ℝ}
    (ht : t ∈ normalizedMaxDomain (fromProjectiveState y) t₀) :
    projectiveOriginalFlow (projectiveReflection y) t₀ t =
      projectiveReflection (projectiveOriginalFlow y t₀ t) := by
  have H := NormalizedSymmetry.swap.maxCurve ht
  change normalizedMaxCurve (axisSwap (fromProjectiveState y)) t₀ t =
    axisSwap (normalizedMaxCurve (fromProjectiveState y) t₀ t) at H
  simp only [projectiveOriginalFlow, fromProjectiveState_reflection, H, toProjectiveState_axisSwap]

/-- Restart at a regular projective state uses the same original Einstein time. -/
theorem projectiveOriginalFlow_restart {y : ProjectiveState} {s t : ℝ}
    (hD : 0 < projectiveStateDenom y) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hA : 0 < 1 + normalizedMaxCurve (fromProjectiveState y) 0 s 0) :
    projectiveOriginalFlow (projectiveOriginalFlow y 0 s) 0 t = projectiveOriginalFlow y 0 (t + s) := by
  have hc := fromProjectiveState_constraint (ne_of_gt hD)
  have hdom := normalizedMaxDomain_contains_Ici_of_constraint hc 0 hs
  have hreconstruct := fromProjectiveState_toProjectiveState (ne_of_gt hA)
    ((normalizedMaxCurve_constraint hdom).trans hc)
  have H := normalizedMaxCurve_shift
    (by simpa only [zero_add] using hdom)
    (normalizedMaxDomain_contains_Ici_of_constraint hc 0 (add_nonneg ht hs))
  simp only [zero_add] at H
  change toProjectiveState (normalizedMaxCurve
    (fromProjectiveState (toProjectiveState (normalizedMaxCurve (fromProjectiveState y) 0 s))) 0 t) = _
  rw [hreconstruct, H]
  rfl

end BianchiIX
