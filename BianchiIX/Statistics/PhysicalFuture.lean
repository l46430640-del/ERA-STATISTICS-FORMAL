import BianchiIX.Statistics.EraJointStatistics
import BianchiIX.Dynamics.AxisPermutations
import BianchiIX.Dynamics.ProjectiveReflection

noncomputable section

namespace BianchiIX

/-- A positive-time point of the exact orbit is a statistical core after a physical axis permutation. -/
def StatisticalCoreFuture (η : ℝ) (J : ℕ) (σ Bcap : ℝ) (x : NormalizedState) : Prop :=
  ∃ T > (0 : ℝ), T ∈ normalizedMaxDomain x 0 ∧
    ∃ i : Fin 6, ∃ p : eraSurvivorDomain η J σ Bcap,
      EraStatistics (EraSurvivor.digits p) (EraSurvivor.phase p) ∧
      coreRadiusEntry p.val.2 = toProjectiveState ((axisFrame i).map (normalizedMaxCurve x 0 T))

theorem statisticalCoreFuture_of_entry_or_reflection {η σ Bcap T : ℝ} {J : ℕ}
    {x : NormalizedState} {p : eraSurvivorDomain η J σ Bcap}
    (ht : 0 < T) (hdom : T ∈ normalizedMaxDomain x 0)
    (hstat : EraStatistics (EraSurvivor.digits p) (EraSurvivor.phase p))
    (ho : coreRadiusEntry p.val.2 = toProjectiveState (normalizedMaxCurve x 0 T) ∨
      coreRadiusEntry p.val.2 = projectiveReflection (toProjectiveState (normalizedMaxCurve x 0 T))) :
    StatisticalCoreFuture η J σ Bcap x := by
  rcases ho with ho | ho
  · exact ⟨T, ht, hdom, 0, p, hstat, ho⟩
  · refine ⟨T, ht, hdom, 3, p, hstat, ?_⟩
    change coreRadiusEntry p.val.2 = toProjectiveState (axisSwap (normalizedMaxCurve x 0 T))
    rw [toProjectiveState_axisSwap]
    exact ho

/-- A finite initial flow segment does not change the later statistical core. -/
theorem StatisticalCoreFuture.of_forward {η σ Bcap s : ℝ} {J : ℕ} {x : NormalizedState}
    (hc : stateConstraint x = 1) (hs : 0 ≤ s)
    (H : StatisticalCoreFuture η J σ Bcap (normalizedMaxCurve x 0 s)) :
    StatisticalCoreFuture η J σ Bcap x := by
  obtain ⟨T, ht, _, i, p, hstat, ho⟩ := H
  have hTs : 0 < T + s := add_pos_of_pos_of_nonneg ht hs
  have hdom := normalizedMaxDomain_contains_Ici_of_constraint hc 0 hTs.le
  have hshift := normalizedMaxCurve_shift (t := T)
    (by simpa only [zero_add] using normalizedMaxDomain_contains_Ici_of_constraint hc 0 hs) hdom
  simp only [zero_add] at hshift
  exact ⟨T + s, hTs, hdom, i, p, hstat, by simpa only [hshift] using ho⟩

end BianchiIX
