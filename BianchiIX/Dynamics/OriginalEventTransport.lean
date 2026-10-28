import BianchiIX.Dynamics.CoreSectionPhysical
import BianchiIX.Dynamics.AxisFrameComposition

noncomputable section

namespace BianchiIX

open Set

theorem normalizedMaxCurve_forward_restart {x y : NormalizedState} {s : ℝ}
    (hc : stateConstraint x = 1) (hs : 0 ≤ s) (hy : y = normalizedMaxCurve x 0 s)
    (t : ℝ) (ht : 0 ≤ t) :
    normalizedMaxCurve y 0 t = normalizedMaxCurve x 0 (t + s) := by
  rw [hy]
  have H := normalizedMaxCurve_shift (t₀ := (0 : ℝ)) (t := t)
    (by simpa only [zero_add] using normalizedMaxDomain_contains_Ici_of_constraint hc 0 hs)
    (normalizedMaxDomain_contains_Ici_of_constraint hc 0 (add_nonneg ht hs))
  simpa only [zero_add] using H

/-- Restarting the clock preserves the first event, not just an event endpoint. -/
theorem first_normalized_event_add_time {x y : NormalizedState} {s T c : ℝ}
    {g : NormalizedState → ℝ} (hc : stateConstraint x = 1) (hs : 0 ≤ s)
    (hy : y = normalizedMaxCurve x 0 s)
    (H : IsLeast {t : ℝ | 0 < t ∧ t ∈ normalizedMaxDomain y 0 ∧ g (normalizedMaxCurve y 0 t) = c} T) :
    IsLeast {t : ℝ | s < t ∧ t ∈ normalizedMaxDomain x 0 ∧ g (normalizedMaxCurve x 0 t) = c} (T + s) := by
  have hcy : stateConstraint y = 1 := hy ▸ (normalizedMaxCurve_forward_of_constraint hc hs).2.1
  refine ⟨⟨by linarith only [H.1.1],
    normalizedMaxDomain_contains_Ici_of_constraint hc 0 (add_nonneg H.1.1.le hs), ?_⟩, ?_⟩
  · rw [← normalizedMaxCurve_forward_restart hc hs hy T H.1.1.le]
    exact H.1.2.2
  · intro t ht
    have hsub : 0 < t - s := sub_pos.mpr ht.1
    have heq := normalizedMaxCurve_forward_restart hc hs hy (t - s) hsub.le
    rw [sub_add_cancel] at heq
    have hle := H.2 ⟨hsub, normalizedMaxDomain_contains_Ici_of_constraint hcy 0 hsub.le,
      by rw [heq]; exact ht.2.2⟩
    linarith only [hle]

theorem normalizedEventRate_add_time {x y : NormalizedState} {s : ℝ}
    (hc : stateConstraint x = 1) (hs : 0 ≤ s) (hy : y = normalizedMaxCurve x 0 s)
    (g : NormalizedState → ℝ) (t : ℝ) (ht : 0 ≤ t) :
    normalizedEventRate g y 0 t = normalizedEventRate g x 0 (t + s) := by
  simp only [normalizedEventRate, normalizedMaxCurve_forward_restart hc hs hy t ht]

/-- A physical frame and a forward restart act on the entire subsequent exact trajectory. -/
theorem axisFrame_forward_restart {x y : NormalizedState} {s : ℝ} (i : Fin 6)
    (hc : stateConstraint x = 1) (hs : 0 ≤ s)
    (hy : y = (axisFrame i).map (normalizedMaxCurve x 0 s)) (t : ℝ) (ht : 0 ≤ t) :
    normalizedMaxCurve y 0 t = (axisFrame i).map (normalizedMaxCurve x 0 (t + s)) := by
  have hy' : y = normalizedMaxCurve ((axisFrame i).map x) 0 s :=
    hy.trans ((axisFrame i).maxCurve (normalizedMaxDomain_contains_Ici_of_constraint hc 0 hs)).symm
  rw [normalizedMaxCurve_forward_restart (((axisFrame i).constraint x).trans hc) hs hy' t ht,
    (axisFrame i).maxCurve (normalizedMaxDomain_contains_Ici_of_constraint hc 0 (add_nonneg ht hs))]

end BianchiIX
