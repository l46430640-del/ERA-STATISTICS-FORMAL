import BianchiIX.Statistics.EraSurvivorOrbit
import BianchiIX.Dynamics.CoreArrivalNonaccumulation
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

namespace EraSurvivor

variable {η σ Bcap : ℝ} {J : ℕ}

theorem budgetState_tendsto_zero (p : eraSurvivorDomain η J σ Bcap) (hcap : Bcap < 1) :
    Tendsto (fun n => (budgetState p n).1) atTop (𝓝 0) := by
  have hp := (budgetState_mem_selected p 0).1.1
  rw [budgetState_zero] at hp
  simp_rw [budgetState_budget, eraAmplitude]
  exact (tendsto_rpow_atTop_of_base_lt_one p.val.1 (by linarith only [hp.1])
    (hp.2.trans_lt hcap)).comp (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 4 / 3))

/-- The explicit arrival schedule escapes every finite original-time interval. -/
theorem elapsedTime_tendsto_atTop (p : eraSurvivorDomain η J σ Bcap) (hcap : Bcap ≤ 1 / 4)
    (hvalid : coreRadiusReturnValid p.val.2) (ht : StrictMono (elapsedTime p))
    (hactual : ∀ n, fromProjectiveState (coreRadiusEntry (state p n)) =
      (axisFrame (frame p n)).map
        (normalizedMaxCurve (fromProjectiveState (coreRadiusEntry p.val.2)) 0 (elapsedTime p n))) :
    Tendsto (elapsedTime p) atTop atTop := by
  have hinput (n : ℕ) := (budgetState_mem_selected p n).1
  have hinit := hinput 0
  rw [budgetState_zero] at hinit
  have hD := coreRadiusReturnValid_denom_pos hvalid
  have hp : positiveWalls (fromProjectiveState (coreRadiusEntry p.val.2)) :=
    fromProjectiveState_positive hD ⟨hinit.2.2.1, by change (0 : ℝ) < 1; norm_num, hinit.2.2.2.1⟩
  apply coreArrivalTime_tendsto_atTop hp (fromProjectiveState_constraint hD.ne') ht.monotone
    (fun n => by simpa only [elapsedTime, Finset.range_zero, Finset.sum_empty] using ht.monotone (Nat.zero_le n))
    (budgetState_tendsto_zero p (hcap.trans_lt (by norm_num))) _ hactual
  intro n
  exact ⟨(hinput n).2.2.1.le, (hinput n).2.2.2.1.le, (hinput n).2.2.2.2.1,
    (hinput n).1.2.trans hcap⟩

end EraSurvivor

/-- All retained infinite histories are actual unbounded-time trajectories, with each selected digit identified by its entry radius. -/
theorem exists_era_survivor_unbounded_orbit :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 20 ≤ J → ∀ σ : ℝ, 0 < σ → σ < 1 → σ * (2 * J : ℕ) < 1 →
        ∃ Bstar > (0 : ℝ), Bstar < 1 ∧ ∀ Bcap : ℝ, Bcap ≤ Bstar →
          ∀ p : eraSurvivorDomain η J σ Bcap,
            (∀ n, 0 < EraSurvivor.duration p n ∧ coreRadiusReturnValid (EraSurvivor.state p n) ∧
              Nat.floor (EraSurvivor.state p n 0 / 2) = (EraSurvivor.digits p n : ℕ)) ∧
            StrictMono (EraSurvivor.elapsedTime p) ∧
            Tendsto (EraSurvivor.elapsedTime p) atTop atTop ∧ ∀ n,
              EraSurvivor.elapsedTime p n ∈ normalizedMaxDomain (fromProjectiveState (coreRadiusEntry p.val.2)) 0 ∧
              fromProjectiveState (coreRadiusEntry (EraSurvivor.state p n)) =
                (axisFrame (EraSurvivor.frame p n)).map (normalizedMaxCurve
                  (fromProjectiveState (coreRadiusEntry p.val.2)) 0 (EraSurvivor.elapsedTime p n)) := by
  obtain ⟨δ, hδ, hδmax, Hδ⟩ := exists_era_survivor_orbit
  refine ⟨δ, hδ, hδmax, ?_⟩
  intro η hη hηδ J hJ σ hσ hσone hσJ
  obtain ⟨Bstar, hB, hBone, HB⟩ := Hδ η hη hηδ J hJ σ hσ hσone hσJ
  refine ⟨min Bstar (1 / 4), lt_min hB (by norm_num), (min_le_left _ _).trans_lt hBone, ?_⟩
  intro Bcap hcap p
  obtain ⟨Hstep, Hmono, Horbit⟩ := HB Bcap (hcap.trans (min_le_left _ _)) p
  have hvalid : coreRadiusReturnValid p.val.2 := by
    simpa only [EraSurvivor.state_zero] using (Hstep 0).2.1
  exact ⟨Hstep, Hmono, EraSurvivor.elapsedTime_tendsto_atTop p
    (hcap.trans (min_le_right _ _)) hvalid Hmono (fun n => (Horbit n).2), Horbit⟩

end BianchiIX
