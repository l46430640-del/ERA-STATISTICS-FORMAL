import BianchiIX.Dynamics.EraEventTimes
import BianchiIX.Dynamics.OriginalEventTransport

noncomputable section

namespace BianchiIX

open Set

def coreOriginalFrame (i : Fin 6) (j : ℕ) : Fin 6 :=
  (axisFrame_comp (corePrefixFrame j) i).choose

namespace EraEventItinerary

variable {η : ℝ} {J m : ℕ} {X : CoreAngleState} (H : EraEventItinerary η J m X)
variable {x : NormalizedState} {s : ℝ} {i : Fin 6}
variable (hc : stateConstraint x = 1) (hs : 0 ≤ s)
variable (hbase : fromProjectiveState (coreRadiusEntry X) =
  (axisFrame i).map (normalizedMaxCurve x 0 s))

include H hc hs hbase

/-- Internal core endpoints expressed in the original initial point's time and physical axis frame. -/
theorem original_core_endpoints (j : ℕ) (hj : j ≤ m) :
    fromProjectiveState (coreRadiusEntry ((coreReflectionState coreRadiusReturnTime)^[j] X)) =
      (axisFrame (coreOriginalFrame i j)).map
        (normalizedMaxCurve x 0 (corePrefixTime j X + s)) ∧
    fromProjectiveState (coreTailEntry (eraCoreExit j X)) =
      (axisFrame (coreOriginalFrame i j)).map
        (normalizedMaxCurve x 0 (coreExitTime j X + s)) := by
  obtain ⟨hp, hin, hout⟩ := H.core_endpoints j hj
  have hd : 0 ≤ coreExitTime j X := hp.trans (H.event_time_order.1 j hj).le
  rw [axisFrame_forward_restart i hc hs hbase _ hp,
    (axisFrame_comp (corePrefixFrame j) i).choose_spec] at hin
  rw [axisFrame_forward_restart i hc hs hbase _ hd,
    (axisFrame_comp (corePrefixFrame j) i).choose_spec] at hout
  exact ⟨hin, hout⟩

/-- The first downward crossing and both transverse directions hold at the absolute core times. -/
theorem original_core_events (j : ℕ) (hj : j ≤ m) :
    let a := corePrefixTime j X + s
    let b := coreExitTime j X + s
    let z := (axisFrame (coreOriginalFrame i j)).map x
    IsLeast {t : ℝ | a < t ∧ t ∈ normalizedMaxDomain z 0 ∧
      projectiveActiveWall (normalizedMaxCurve z 0 t) = 1} b ∧
      0 < normalizedEventRate projectiveActiveWall z 0 a ∧
      normalizedEventRate projectiveActiveWall z 0 b < 0 := by
  intro a b z
  have ha : 0 ≤ a := add_nonneg (H.core_endpoints j hj).1 hs
  have hcz : stateConstraint z = 1 := ((axisFrame (coreOriginalFrame i j)).constraint x).trans hc
  have hstart : fromProjectiveState (coreRadiusEntry ((coreReflectionState coreRadiusReturnTime)^[j] X)) =
      normalizedMaxCurve z 0 a :=
    (H.original_core_endpoints hc hs hbase j hj).1.trans
      ((axisFrame (coreOriginalFrame i j)).maxCurve
        (normalizedMaxDomain_contains_Ici_of_constraint hc 0 ha)).symm
  have HV := (H.core j hj).2.2.1
  have hf := first_normalized_event_add_time hcz ha hstart HV.1
  have hr0 := normalizedEventRate_add_time hcz ha hstart projectiveActiveWall 0 le_rfl
  have hrT := normalizedEventRate_add_time hcz ha hstart projectiveActiveWall _ HV.1.1.1.le
  refine ⟨?_, ?_, ?_⟩
  · simpa only [coreExitTime, a, b, add_assoc] using hf
  · simp only [zero_add] at hr0
    exact hr0 ▸ (H.core j hj).2.1.2
  · simpa only [coreExitTime, a, b, add_assoc, ← hrT] using HV.2.2.2

/-- Transfer a connection after a specified physical axis change to its absolute first arrival. -/
theorem original_exit_connection (j : ℕ) (hj : j ≤ m) (k : Fin 6) (T : ℝ)
    (HF : IsLeast {t : ℝ | 0 < t ∧
      t ∈ normalizedMaxDomain ((axisFrame k).map (fromProjectiveState (coreTailEntry (eraCoreExit j X)))) 0 ∧
      projectiveActiveWall (normalizedMaxCurve
        ((axisFrame k).map (fromProjectiveState (coreTailEntry (eraCoreExit j X)))) 0 t) = 1} T)
    (HU : 0 < normalizedEventRate projectiveActiveWall
      ((axisFrame k).map (fromProjectiveState (coreTailEntry (eraCoreExit j X)))) 0 T) :
    let b := coreExitTime j X + s
    let z := (axisFrame (axisFrame_comp k (coreOriginalFrame i j)).choose).map x
    IsLeast {t : ℝ | b < t ∧ t ∈ normalizedMaxDomain z 0 ∧
      projectiveActiveWall (normalizedMaxCurve z 0 t) = 1} (T + b) ∧
      0 < normalizedEventRate projectiveActiveWall z 0 (T + b) := by
  intro b z
  have hb : 0 ≤ b := add_nonneg
    ((H.core_endpoints j hj).1.trans (H.event_time_order.1 j hj).le) hs
  have hcz : stateConstraint z = 1 :=
    ((axisFrame (axisFrame_comp k (coreOriginalFrame i j)).choose).constraint x).trans hc
  have hstart : (axisFrame k).map (fromProjectiveState (coreTailEntry (eraCoreExit j X))) =
      normalizedMaxCurve z 0 b := by
    rw [(H.original_core_endpoints hc hs hbase j hj).2,
      (axisFrame_comp k (coreOriginalFrame i j)).choose_spec]
    exact ((axisFrame (axisFrame_comp k (coreOriginalFrame i j)).choose).maxCurve
      (normalizedMaxDomain_contains_Ici_of_constraint hc 0 hb)).symm
  exact ⟨first_normalized_event_add_time hcz hb hstart HF,
    (normalizedEventRate_add_time hcz hb hstart projectiveActiveWall T HF.1.1.le) ▸ HU⟩

theorem original_reflection_events (j : ℕ) (hj : j < m) :
    let b := coreExitTime j X + s
    let a := corePrefixTime (j + 1) X + s
    let z := (axisFrame (axisFrame_comp 3 (coreOriginalFrame i j)).choose).map x
    IsLeast {t : ℝ | b < t ∧ t ∈ normalizedMaxDomain z 0 ∧
      projectiveActiveWall (normalizedMaxCurve z 0 t) = 1} a ∧
      0 < normalizedEventRate projectiveActiveWall z 0 a := by
  have HT := H.original_exit_connection hc hs hbase j hj.le 3
    (reflectionReturnTime (eraCoreExit j X)) (H.reflection j hj).2.1 (H.reflection_upward j hj)
  simpa only [corePrefixTime_succ, coreReflectionTime, coreExitTime, eraCoreExit,
    Function.comp_apply, add_assoc] using HT

theorem original_terminal_event :
    let b := coreExitTime m X + s
    let a := eraReturnTime η J m X + s
    let z := (axisFrame (axisFrame_comp 1 (coreOriginalFrame i m)).choose).map x
    IsLeast {t : ℝ | b < t ∧ t ∈ normalizedMaxDomain z 0 ∧
      projectiveActiveWall (normalizedMaxCurve z 0 t) = 1} a ∧
      0 < normalizedEventRate projectiveActiveWall z 0 a := by
  have HT := H.original_exit_connection hc hs hbase m le_rfl 1
    (terminalNaturalTime η J (eraCoreExit m X)) H.terminal.2.1 H.terminal.2.2.2.2
  simpa only [eraReturnTime, coreExitTime, add_assoc] using HT

end EraEventItinerary
end BianchiIX
