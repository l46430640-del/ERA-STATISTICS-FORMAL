import BianchiIX.Dynamics.OriginalEraEvents
import BianchiIX.Statistics.CoreRestartOrbit
import BianchiIX.Statistics.EraStatisticsShift

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

/-- Complete eras on one original physical trajectory, including the terminal connection before the first era. -/
structure PhysicalEraSequence (η : ℝ) (J : ℕ) (x : NormalizedState)
    (K : ℕ → ℕ+) (Y : ℕ → CoreAngleState) (t : ℕ → ℝ) (a : ℕ → Fin 6) : Prop where
  constraint : stateConstraint x = 1
  statistics : EraStatistics K (fun n => 2 / Y n 0)
  time_positive : ∀ n, 0 < t n
  time_strictMono : StrictMono t
  time_unbounded : Tendsto t atTop atTop
  entrance : ∀ n, fromProjectiveState (coreRadiusEntry (Y n)) =
    (axisFrame (a n)).map (normalizedMaxCurve x 0 (t n))
  block : ∀ n, EraEventItinerary η J (K n).natPred (Y n)
  next_state : ∀ n, coreRadiusEntry (Y (n + 1)) = terminalNaturalState η J
    (eraCoreExit (K n).natPred (Y n))
  next_time : ∀ n, t (n + 1) = eraReturnTime η J (K n).natPred (Y n) + t n
  next_frame : ∀ n z, (axisFrame (a (n + 1))).map z =
    (axisFrame (eraReturnFrame (K n).natPred)).map ((axisFrame (a n)).map z)
  preceding_terminal : ∃ m X s i, EraEventItinerary η J m X ∧ 0 < s ∧ s < t 0 ∧
    fromProjectiveState (coreRadiusEntry X) = (axisFrame i).map (normalizedMaxCurve x 0 s) ∧
    t 0 = eraReturnTime η J m X + s ∧
    coreRadiusEntry (Y 0) = terminalNaturalState η J (eraCoreExit m X) ∧
    ∀ z, (axisFrame (a 0)).map z = (axisFrame (eraReturnFrame m)).map ((axisFrame i).map z)

namespace EraSurvivor

variable {η σ Bcap : ℝ} {J : ℕ}

theorem physicalTime_succ (w : CoreRestartData) (p : eraSurvivorDomain η J σ Bcap) (n : ℕ) :
    physicalTime w p (n + 1) = duration p n + physicalTime w p n := by
  simp only [physicalTime, elapsedTime_succ, add_assoc]

theorem physicalFrame_succ (w : CoreRestartData) (p : eraSurvivorDomain η J σ Bcap) (n : ℕ) (z : NormalizedState) :
    (axisFrame (physicalFrame w p (n + 1))).map z =
      (axisFrame (eraReturnFrame (digits p n).natPred)).map ((axisFrame (physicalFrame w p n)).map z) := by
  rw [physicalFrame, ← (axisFrame_comp (frame p (n + 1)) w.1.1).choose_spec, frame_succ,
    (axisFrame_comp (frame p n) w.1.1).choose_spec]
  rfl

/-- Removing the initial block leaves complete eras with the same full statistics and an actual preceding terminal connection. -/
theorem physical_era_sequence {x : NormalizedState} (w : CoreRestartData)
    (p : eraSurvivorDomain η J σ Bcap) (hc : stateConstraint x = 1)
    (Hstat : EraStatistics (digits p) (phase p))
    (Hblocks : ∀ n, EraEventItinerary η J (digits p n).natPred (state p n) ∧
      coreRadiusEntry (state p (n + 1)) = terminalNaturalState η J (eraCoreExit (digits p n).natPred (state p n)))
    (Hmono : StrictMono (physicalTime w p))
    (Htop : Tendsto (physicalTime w p) atTop atTop)
    (Hactual : ∀ n, 0 < physicalTime w p n ∧
      fromProjectiveState (coreRadiusEntry (state p n)) =
        (axisFrame (physicalFrame w p n)).map (normalizedMaxCurve x 0 (physicalTime w p n))) :
    PhysicalEraSequence η J x (fun n => digits p (n + 1)) (fun n => state p (n + 1))
      (fun n => physicalTime w p (n + 1)) (fun n => physicalFrame w p (n + 1)) := by
  refine ⟨hc, ?_, fun n => (Hactual (n + 1)).1, ?_, ?_, fun n => (Hactual (n + 1)).2,
    fun n => (Hblocks (n + 1)).1, fun n => (Hblocks (n + 1)).2,
    fun n => physicalTime_succ w p (n + 1), fun n z => physicalFrame_succ w p (n + 1) z, ?_⟩
  · have HT := (eraStatistics_shift_iff (digits p) (phase p) 1).mpr Hstat
    change EraStatistics (fun n => digits p (1 + n)) (fun n => 2 / state p (1 + n) 0) at HT
    simpa only [Nat.add_comm 1] using HT
  · exact fun i j hij => Hmono (Nat.add_lt_add_right hij 1)
  · exact Htop.comp (tendsto_add_atTop_nat 1)
  · exact ⟨(digits p 0).natPred, state p 0, physicalTime w p 0, physicalFrame w p 0,
      (Hblocks 0).1, (Hactual 0).1, Hmono (by omega), (Hactual 0).2,
      physicalTime_succ w p 0, (Hblocks 0).2, fun z => physicalFrame_succ w p 0 z⟩

end EraSurvivor

namespace PhysicalEraSequence

variable {η : ℝ} {J : ℕ} {x : NormalizedState} {K : ℕ → ℕ+} {Y : ℕ → CoreAngleState}
variable {t : ℕ → ℝ} {a : ℕ → Fin 6} (H : PhysicalEraSequence η J x K Y t a)

include H

theorem core_count (n : ℕ) :
    ((Finset.range (K n : ℕ)).image (fun j => corePrefixTime j (Y n) + t n)).card = (K n : ℕ) := by
  classical
  simpa only [(H.block n).count, PNat.natPred_add_one] using (H.block n).core_entrance_count (t n)

theorem digit_eq_floor (n : ℕ) : (K n : ℕ) = Nat.floor (Y n 0 / 2) := by
  simpa only [PNat.natPred_add_one] using (H.block n).count.symm

theorem core_events (n j : ℕ) (hj : j ≤ (K n).natPred) :
    let u := corePrefixTime j (Y n) + t n
    let v := coreExitTime j (Y n) + t n
    let z := (axisFrame (coreOriginalFrame (a n) j)).map x
    IsLeast {s : ℝ | u < s ∧ s ∈ normalizedMaxDomain z 0 ∧
      projectiveActiveWall (normalizedMaxCurve z 0 s) = 1} v ∧
      0 < normalizedEventRate projectiveActiveWall z 0 u ∧
      normalizedEventRate projectiveActiveWall z 0 v < 0 :=
  (H.block n).original_core_events H.constraint (H.time_positive n).le (H.entrance n) j hj

theorem reflection_events (n j : ℕ) (hj : j < (K n).natPred) :
    let v := coreExitTime j (Y n) + t n
    let u := corePrefixTime (j + 1) (Y n) + t n
    let z := (axisFrame (axisFrame_comp 3 (coreOriginalFrame (a n) j)).choose).map x
    IsLeast {s : ℝ | v < s ∧ s ∈ normalizedMaxDomain z 0 ∧
      projectiveActiveWall (normalizedMaxCurve z 0 s) = 1} u ∧
      0 < normalizedEventRate projectiveActiveWall z 0 u :=
  (H.block n).original_reflection_events H.constraint (H.time_positive n).le (H.entrance n) j hj

theorem terminal_event (n : ℕ) :
    let v := coreExitTime (K n).natPred (Y n) + t n
    let z := (axisFrame (a (n + 1))).map x
    IsLeast {s : ℝ | v < s ∧ s ∈ normalizedMaxDomain z 0 ∧
      projectiveActiveWall (normalizedMaxCurve z 0 s) = 1} (t (n + 1)) ∧
      0 < normalizedEventRate projectiveActiveWall z 0 (t (n + 1)) := by
  have hframe : (axisFrame (axisFrame_comp 1 (coreOriginalFrame (a n) (K n).natPred)).choose).map x =
      (axisFrame (a (n + 1))).map x := by
    rw [← (axisFrame_comp 1 (coreOriginalFrame (a n) (K n).natPred)).choose_spec,
      H.next_frame n x, eraReturnFrame_apply]
    change axisCycle ((axisFrame (coreOriginalFrame (a n) (K n).natPred)).map x) = _
    rw [coreOriginalFrame, ← (axisFrame_comp (corePrefixFrame (K n).natPred) (a n)).choose_spec]
  have HT := (H.block n).original_terminal_event H.constraint (H.time_positive n).le (H.entrance n)
  simpa only [hframe, ← H.next_time n] using HT

end PhysicalEraSequence
end BianchiIX
