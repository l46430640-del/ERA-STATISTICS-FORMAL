import BianchiIX.Dynamics.EraEventItinerary
import Mathlib.Order.Interval.Set.Monotone

noncomputable section

namespace BianchiIX

/-- Original time of the downward exit of core `j`, measured from the block's initial core. -/
def coreExitTime (j : ℕ) (X : CoreAngleState) : ℝ :=
  coreRadiusReturnTime ((coreReflectionState coreRadiusReturnTime)^[j] X) + corePrefixTime j X

namespace EraEventItinerary

variable {η : ℝ} {J m : ℕ} {X : CoreAngleState} (H : EraEventItinerary η J m X)

include H

theorem reflection_time_pos (j : ℕ) (hj : j < m) :
    0 < coreReflectionTime ((coreReflectionState coreRadiusReturnTime)^[j] X) :=
  add_pos (H.reflection j hj).2.1.1.1 (H.core j hj.le).2.2.1.1.1.1

/-- Each internal upward and downward event is on the same physical orbit in its accumulated frame. -/
theorem core_endpoints (j : ℕ) (hj : j ≤ m) :
    0 ≤ corePrefixTime j X ∧
      fromProjectiveState (coreRadiusEntry ((coreReflectionState coreRadiusReturnTime)^[j] X)) =
        (axisFrame (corePrefixFrame j)).map
          (normalizedMaxCurve (fromProjectiveState (coreRadiusEntry X)) 0 (corePrefixTime j X)) ∧
      fromProjectiveState (coreTailEntry (eraCoreExit j X)) = (axisFrame (corePrefixFrame j)).map
        (normalizedMaxCurve (fromProjectiveState (coreRadiusEntry X)) 0 (coreExitTime j X)) := by
  obtain ⟨hp, hend⟩ := corePrefix_normalized_endpoint
    (fun i hi => (H.core i (hi.trans hj)).2.2.1)
    (fun i hi => ⟨H.reflection_time_pos i (hi.trans_le hj), by
      simpa only [Function.iterate_succ_apply'] using (H.reflection i (hi.trans_le hj)).2.2.2⟩)
  have hvalid := (H.core j hj).2.2.1
  have hc := fromProjectiveState_constraint (coreRadiusReturnValid_denom_pos (H.core 0 (Nat.zero_le _)).2.2.1).ne'
  change stateConstraint (fromProjectiveState (coreRadiusEntry X)) = 1 at hc
  have hdown := hvalid.1.1.1
  have hS : 0 < coreExitTime j X := add_pos_of_pos_of_nonneg hdown hp
  have hcP := (normalizedMaxCurve_forward_of_constraint hc hp).2.1
  have hshift := normalizedMaxCurve_shift (t₀ := (0 : ℝ))
    (t := coreRadiusReturnTime ((coreReflectionState coreRadiusReturnTime)^[j] X))
    (by simpa only [zero_add] using normalizedMaxDomain_contains_Ici_of_constraint hc 0 hp)
    (normalizedMaxDomain_contains_Ici_of_constraint hc 0 hS.le)
  simp only [zero_add] at hshift
  refine ⟨hp, hend, ?_⟩
  change fromProjectiveState (coreTailEntry
    (coreReturnState coreRadiusReturnTime ((coreReflectionState coreRadiusReturnTime)^[j] X))) = _
  rw [coreReturn_normalized_endpoint hvalid (H.core j hj).2.2.2, hend,
    (axisFrame (corePrefixFrame j)).maxCurve
      (normalizedMaxDomain_contains_Ici_of_constraint hcP 0 hdown.le), hshift]
  rfl

theorem reflection_upward (j : ℕ) (hj : j < m) :
    let Z := eraCoreExit j X
    let x := axisSwap (fromProjectiveState (coreTailEntry Z))
    0 < normalizedEventRate projectiveActiveWall x 0 (reflectionReturnTime Z) := by
  intro Z x
  have hcore := (H.core j hj.le).2.2.1
  have hdown := coreReturn_normalized_endpoint hcore (H.core j hj.le).2.2.2
  change fromProjectiveState (coreTailEntry Z) = _ at hdown
  have hc : stateConstraint x = 1 := by
    rw [show x = axisSwap (fromProjectiveState (coreTailEntry Z)) from rfl, axisSwap_constraint, hdown]
    exact (normalizedMaxCurve_forward_of_constraint
      (fromProjectiveState_constraint (coreRadiusReturnValid_denom_pos hcore).ne') hcore.1.1.1.le).2.1
  have hproj := (H.reflection j hj).2.2.1
  change toProjectiveState (normalizedMaxCurve x 0 (reflectionReturnTime Z)) =
    coreRadiusEntry ((coreReflectionState coreRadiusReturnTime)^[j + 1] X) at hproj
  have hunit : toProjectiveState (normalizedMaxCurve x 0 (reflectionReturnTime Z)) 2 = 1 :=
    congrFun hproj 2
  have hrec := fromProjectiveState_toProjectiveState (unit_active_wall_clock_ne_zero hunit)
    ((normalizedMaxCurve_forward_of_constraint hc (H.reflection j hj).2.1.1.1.le).2.1)
  rw [hproj] at hrec
  have hup := (H.core (j + 1) (by omega)).2.1.2
  rw [normalizedEventRate, normalizedMaxCurve_initial] at hup
  change 0 < fderiv ℝ projectiveActiveWall _ (normalizedField _)
  rwa [← hrec]

/-- Each core exit lies strictly between its own entrance and the next entrance; the last exit precedes the terminal arrival. -/
theorem event_time_order :
    (∀ j ≤ m, corePrefixTime j X < coreExitTime j X) ∧
      (∀ j < m, coreExitTime j X < corePrefixTime (j + 1) X) ∧
      coreExitTime m X < eraReturnTime η J m X := by
  refine ⟨?_, ?_, ?_⟩
  · intro j hj
    have ht := (H.core j hj).2.2.1.1.1.1
    change corePrefixTime j X < coreRadiusReturnTime _ + corePrefixTime j X
    linarith only [ht]
  · intro j hj
    have ht := (H.reflection j hj).2.1.1.1
    rw [corePrefixTime_succ]
    dsimp only [coreExitTime, coreReflectionTime]
    linarith only [ht]
  · have ht := H.terminal.2.1.1.1
    change coreExitTime m X < terminalNaturalTime η J (eraCoreExit m X) + coreExitTime m X
    linarith only [ht]

theorem prefixTime_strictMonoOn : StrictMonoOn (fun j => corePrefixTime j X) (Set.Iic m) := by
  apply strictMonoOn_Iic_of_lt_succ
  intro j hj
  exact (H.event_time_order.1 j hj.le).trans (H.event_time_order.2.1 j hj)

/-- The physical entrance times are distinct and their number is the entry-radius digit, for every time origin. -/
theorem core_entrance_count (s : ℝ) :
    ((Finset.range (m + 1)).image (fun j => corePrefixTime j X + s)).card = Nat.floor (X 0 / 2) := by
  classical
  have hinj : Set.InjOn (fun j => corePrefixTime j X + s) (↑(Finset.range (m + 1)) : Set ℕ) := by
    intro i hi j hj hij
    exact H.prefixTime_strictMonoOn.injOn (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
      (Nat.le_of_lt_succ (Finset.mem_range.mp hj)) (add_right_cancel hij)
  rw [Finset.card_image_of_injOn hinj, Finset.card_range, H.count]

end EraEventItinerary
end BianchiIX
