import BianchiIX.Dynamics.LateAxisCrossing

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

def WallProductDecay (x : NormalizedState) : Prop :=
  ∀ i j : Fin 3, i ≠ j → Tendsto
    (fun t => wallValue i (normalizedMaxCurve x 0 t) * wallValue j (normalizedMaxCurve x 0 t))
      atTop (𝓝 0)

/-- Decay of the wall products is independent of every existing finite time origin. -/
theorem wallProductDecay_maxCurve_iff {x : NormalizedState} {s : ℝ}
    (hc : stateConstraint x = 1) (hs : s ∈ normalizedMaxDomain x 0) :
    WallProductDecay (normalizedMaxCurve x 0 s) ↔ WallProductDecay x := by
  unfold WallProductDecay
  refine forall_congr' (fun i => forall_congr' (fun j => forall_congr' (fun _ => ?_)))
  have heq :
      (fun t => wallValue i (normalizedMaxCurve (normalizedMaxCurve x 0 s) 0 t) *
        wallValue j (normalizedMaxCurve (normalizedMaxCurve x 0 s) 0 t)) =ᶠ[atTop]
      (fun t => wallValue i (normalizedMaxCurve x 0 (t + s)) *
        wallValue j (normalizedMaxCurve x 0 (t + s))) := by
    filter_upwards [eventually_ge_atTop (-s)] with t ht
    have hdom := normalizedMaxDomain_contains_Ici_of_constraint hc 0 (show 0 ≤ t + s by linarith)
    have H := normalizedMaxCurve_shift (by simpa only [zero_add] using hs) hdom
    simpa only [zero_add] using congrArg (fun z => wallValue i z * wallValue j z) H
  rw [tendsto_congr' heq]
  change Tendsto ((fun t => wallValue i (normalizedMaxCurve x 0 t) *
    wallValue j (normalizedMaxCurve x 0 t)) ∘ (fun t => t + s)) atTop (𝓝 0) ↔ _
  rw [← tendsto_map'_iff, map_add_atTop_eq]

theorem WallProductDecay.axisPermutation {x : NormalizedState}
    (H : WallProductDecay x) (hp : positiveWalls x) (hc : stateConstraint x = 1)
    (σ : Equiv.Perm (Fin 3)) : WallProductDecay ((axisPermutation σ).map x) :=
  wallProductDecay_axisPermutation hp hc H σ

end BianchiIX
