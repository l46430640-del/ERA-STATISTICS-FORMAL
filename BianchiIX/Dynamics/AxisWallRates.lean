import BianchiIX.Dynamics.SmallWallEntry
import BianchiIX.Dynamics.AxisFrameComposition

noncomputable section

namespace BianchiIX

theorem axisFrame_wallRate {x : NormalizedState} (hp : positiveWalls x) (a : Fin 6) (i : Fin 3) :
    wallRate i ((axisFrame a).map x) = wallRate (axisOrder a i) x := by
  have hfield (j : Fin 3) (y : NormalizedState) :
      wallValue j (normalizedField y) = wallRate j y * wallValue j y := by
    fin_cases j <;> rfl
  have hpos (j : Fin 3) : 0 < wallValue j x := by
    fin_cases j
    · exact hp.1
    · exact hp.2.1
    · exact hp.2.2
  have H := congrArg (wallValue i) ((axisFrame a).field x)
  rw [hfield, axisFrame_wallValue, axisFrame_wallValue, hfield] at H
  exact mul_right_cancel₀ (hpos (axisOrder a i)).ne' H

theorem exists_axisFrame_first_wall (i : Fin 3) : ∃ a : Fin 6, axisOrder a 0 = i := by
  fin_cases i
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩

/-- A future wall-product bound survives a restart of the same constrained orbit. -/
theorem normalizedWallProductsBound.forward {x : NormalizedState} {Δ s : ℝ}
    (hc : stateConstraint x = 1)
    (H : ∀ u ≥ (0 : ℝ), normalizedWallProductsBound Δ (normalizedMaxCurve x 0 u))
    (hs : 0 ≤ s) :
    ∀ u ≥ (0 : ℝ), normalizedWallProductsBound Δ
      (normalizedMaxCurve (normalizedMaxCurve x 0 s) 0 u) := by
  intro u hu
  have hdom := normalizedMaxDomain_contains_Ici_of_constraint hc 0 hs
  have hcs : stateConstraint (normalizedMaxCurve x 0 s) = 1 :=
    (normalizedMaxCurve_constraint hdom).trans hc
  have heq := (normalizedMaxCurve_restart (t := s + u) hdom (by
    simpa only [add_sub_cancel_left] using normalizedMaxDomain_contains_Ici_of_constraint hcs 0 hu)).2
  simp only [add_sub_cancel_left] at heq
  rw [← heq]
  exact H _ (add_nonneg hs hu)

end BianchiIX
