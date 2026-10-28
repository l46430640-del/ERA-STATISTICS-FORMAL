import BianchiIX.Statistics.CoreRestartWitness
import BianchiIX.Statistics.EraSurvivorNonaccumulation

noncomputable section

namespace BianchiIX

open Filter
open scoped Topology

namespace EraSurvivor

variable {η σ Bcap : ℝ} {J : ℕ}

def physicalTime (w : CoreRestartData) (p : eraSurvivorDomain η J σ Bcap) (n : ℕ) : ℝ :=
  elapsedTime p n + w.1.2

def physicalFrame (w : CoreRestartData) (p : eraSurvivorDomain η J σ Bcap) (n : ℕ) : Fin 6 :=
  (axisFrame_comp (frame p n) w.1.1).choose

end EraSurvivor

/-- Restore the original initial point and its chosen axis frame for every later core arrival. -/
theorem CoreRestartWitness.physical_orbit {η σ Bcap : ℝ} {J : ℕ}
    {x : NormalizedState} {w : CoreRestartData} (H : CoreRestartWitness η J σ Bcap x w)
    (hc : stateConstraint x = 1) (p : eraSurvivorDomain η J σ Bcap) (hp : p.val = w.2)
    (hmono : StrictMono (EraSurvivor.elapsedTime p))
    (htop : Tendsto (EraSurvivor.elapsedTime p) atTop atTop)
    (horbit : ∀ n, fromProjectiveState (coreRadiusEntry (EraSurvivor.state p n)) =
      (axisFrame (EraSurvivor.frame p n)).map (normalizedMaxCurve
        (fromProjectiveState (coreRadiusEntry p.val.2)) 0 (EraSurvivor.elapsedTime p n))) :
    StrictMono (EraSurvivor.physicalTime w p) ∧
      Tendsto (EraSurvivor.physicalTime w p) atTop atTop ∧ ∀ n,
        0 < EraSurvivor.physicalTime w p n ∧
        EraSurvivor.physicalTime w p n ∈ normalizedMaxDomain x 0 ∧
        fromProjectiveState (coreRadiusEntry (EraSurvivor.state p n)) =
          (axisFrame (EraSurvivor.physicalFrame w p n)).map
            (normalizedMaxCurve x 0 (EraSurvivor.physicalTime w p n)) := by
  obtain ⟨hτ, hdom, q, hq, _, hproj⟩ := H
  have hproj' : coreRadiusEntry p.val.2 =
      toProjectiveState ((axisFrame w.1.1).map (normalizedMaxCurve x 0 w.1.2)) := by
    rw [hp, ← hq]
    exact hproj
  have hcτ : stateConstraint (normalizedMaxCurve x 0 w.1.2) = 1 :=
    (normalizedMaxCurve_constraint hdom).trans hc
  have hbase : fromProjectiveState (coreRadiusEntry p.val.2) =
      (axisFrame w.1.1).map (normalizedMaxCurve x 0 w.1.2) := by
    have hunit : toProjectiveState ((axisFrame w.1.1).map (normalizedMaxCurve x 0 w.1.2)) 2 = 1 := by
      rw [← hproj']
      rfl
    rw [hproj', fromProjectiveState_toProjectiveState (unit_active_wall_clock_ne_zero hunit)
      (((axisFrame w.1.1).constraint _).trans hcτ)]
  have hn (n : ℕ) : 0 ≤ EraSurvivor.elapsedTime p n := by
    simpa only [EraSurvivor.elapsedTime, Finset.range_zero, Finset.sum_empty] using hmono.monotone (Nat.zero_le n)
  refine ⟨fun i j hij => by dsimp only [EraSurvivor.physicalTime]; linarith only [hmono hij],
    tendsto_atTop_add_const_right atTop w.1.2 htop, ?_⟩
  intro n
  have hpos : 0 < EraSurvivor.physicalTime w p n := add_pos_of_nonneg_of_pos (hn n) hτ
  have htime := normalizedMaxDomain_contains_Ici_of_constraint hc 0 hpos.le
  have hshift := normalizedMaxCurve_shift (t₀ := (0 : ℝ)) (t := EraSurvivor.elapsedTime p n)
    (by simpa only [zero_add] using hdom) htime
  simp only [zero_add] at hshift
  refine ⟨hpos, htime, ?_⟩
  have Hn := horbit n
  rw [hbase, (axisFrame w.1.1).maxCurve
    (normalizedMaxDomain_contains_Ici_of_constraint hcτ 0 (hn n)), hshift,
    (axisFrame_comp (EraSurvivor.frame p n) w.1.1).choose_spec] at Hn
  exact Hn

end BianchiIX
