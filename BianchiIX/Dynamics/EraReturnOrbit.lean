import BianchiIX.Dynamics.CorePrefixOrbit
import BianchiIX.Dynamics.EraBoundedPhase

noncomputable section

namespace BianchiIX

/-- The full original time includes every reflection, the last downward core, and the terminal connection. -/
def eraReturnTime (η : ℝ) (J m : ℕ) (X : CoreAngleState) : ℝ :=
  terminalNaturalTime η J (eraCoreExit m X) +
    (coreRadiusReturnTime ((coreReflectionState coreRadiusReturnTime)^[m] X) + corePrefixTime m X)

def eraReturnFrame (m : ℕ) : Fin 6 := (axisFrame_comp 1 (corePrefixFrame m)).choose

theorem eraReturnFrame_apply (m : ℕ) (x : NormalizedState) :
    (axisFrame (eraReturnFrame m)).map x = axisCycle ((axisFrame (corePrefixFrame m)).map x) :=
  ((axisFrame_comp 1 (corePrefixFrame m)).choose_spec x).symm

/-- The local event identities compose in normalized time, without requiring one projective chart along the entire era. -/
theorem eraReturn_normalized_endpoint {η : ℝ} {J m : ℕ} {X : CoreAngleState}
    (Hvalid : ∀ j ≤ m, coreRadiusReturnValid ((coreReflectionState coreRadiusReturnTime)^[j] X))
    (Hconn : ∀ j < m,
      let Y := (coreReflectionState coreRadiusReturnTime)^[j] X
      0 < coreReflectionTime Y ∧
        coreRadiusEntry (coreReflectionState coreRadiusReturnTime Y) = projectiveReflection
          (projectiveOriginalFlow (coreRadiusEntry Y) 0 (coreReflectionTime Y)))
    (hchart : coreTailEntry (eraCoreExit m X) = projectiveOriginalFlow
      (coreRadiusEntry ((coreReflectionState coreRadiusReturnTime)^[m] X)) 0
      (coreRadiusReturnTime ((coreReflectionState coreRadiusReturnTime)^[m] X)))
    (hT : 0 < terminalNaturalTime η J (eraCoreExit m X))
    (hactual : toProjectiveState (normalizedMaxCurve
      (axisCycle (fromProjectiveState (coreTailEntry (eraCoreExit m X)))) 0
      (terminalNaturalTime η J (eraCoreExit m X))) = terminalNaturalState η J (eraCoreExit m X))
    (hunit : terminalNaturalState η J (eraCoreExit m X) 2 = 1) :
    0 < eraReturnTime η J m X ∧
      eraReturnTime η J m X ∈ normalizedMaxDomain (fromProjectiveState (coreRadiusEntry X)) 0 ∧
      fromProjectiveState (terminalNaturalState η J (eraCoreExit m X)) =
        (axisFrame (eraReturnFrame m)).map
          (normalizedMaxCurve (fromProjectiveState (coreRadiusEntry X)) 0 (eraReturnTime η J m X)) := by
  let x := fromProjectiveState (coreRadiusEntry X)
  let S := coreRadiusReturnTime ((coreReflectionState coreRadiusReturnTime)^[m] X) + corePrefixTime m X
  let T := terminalNaturalTime η J (eraCoreExit m X)
  have hc : stateConstraint x = 1 :=
    fromProjectiveState_constraint (coreRadiusReturnValid_denom_pos (Hvalid 0 (Nat.zero_le _))).ne'
  obtain ⟨hp, hprefix⟩ := corePrefix_normalized_endpoint Hvalid Hconn
  have hdown := (Hvalid m le_rfl).1.1.1
  have hS : 0 < S := add_pos_of_pos_of_nonneg hdown hp
  have hcP : stateConstraint (normalizedMaxCurve x 0 (corePrefixTime m X)) = 1 :=
    (normalizedMaxCurve_forward_of_constraint hc hp).2.1
  have hshift := normalizedMaxCurve_shift (t₀ := (0 : ℝ))
    (t := coreRadiusReturnTime ((coreReflectionState coreRadiusReturnTime)^[m] X))
    (by simpa only [zero_add] using normalizedMaxDomain_contains_Ici_of_constraint hc 0 hp)
    (normalizedMaxDomain_contains_Ici_of_constraint hc 0 hS.le)
  simp only [zero_add] at hshift
  have hexit : fromProjectiveState (coreTailEntry (eraCoreExit m X)) =
      (axisFrame (corePrefixFrame m)).map (normalizedMaxCurve x 0 S) := by
    change fromProjectiveState (coreTailEntry
      (coreReturnState coreRadiusReturnTime ((coreReflectionState coreRadiusReturnTime)^[m] X))) = _
    rw [coreReturn_normalized_endpoint (Hvalid m le_rfl) hchart, hprefix,
      (axisFrame (corePrefixFrame m)).maxCurve
        (normalizedMaxDomain_contains_Ici_of_constraint hcP 0 hdown.le), hshift]
  have hstart : axisCycle (fromProjectiveState (coreTailEntry (eraCoreExit m X))) =
      (axisFrame (eraReturnFrame m)).map (normalizedMaxCurve x 0 S) := by
    rw [hexit, eraReturnFrame_apply]
  have hcS : stateConstraint (normalizedMaxCurve x 0 S) = 1 :=
    (normalizedMaxCurve_forward_of_constraint hc hS.le).2.1
  have hsum : 0 < eraReturnTime η J m X := add_pos hT hS
  have hflow : normalizedMaxCurve
      (axisCycle (fromProjectiveState (coreTailEntry (eraCoreExit m X)))) 0 T =
        (axisFrame (eraReturnFrame m)).map (normalizedMaxCurve x 0 (eraReturnTime η J m X)) := by
    rw [hstart, (axisFrame (eraReturnFrame m)).maxCurve
      (normalizedMaxDomain_contains_Ici_of_constraint hcS 0 hT.le)]
    have H := normalizedMaxCurve_shift (t₀ := (0 : ℝ)) (t := T)
      (by simpa only [zero_add] using normalizedMaxDomain_contains_Ici_of_constraint hc 0 hS.le)
      (normalizedMaxDomain_contains_Ici_of_constraint hc 0 hsum.le)
    simpa only [zero_add, eraReturnTime, S, T] using congrArg (axisFrame (eraReturnFrame m)).map H
  have hcend : stateConstraint (normalizedMaxCurve
      (axisCycle (fromProjectiveState (coreTailEntry (eraCoreExit m X)))) 0 T) = 1 := by
    rw [hflow, (axisFrame (eraReturnFrame m)).constraint]
    exact (normalizedMaxCurve_forward_of_constraint hc hsum.le).2.1
  refine ⟨hsum, normalizedMaxDomain_contains_Ici_of_constraint hc 0 hsum.le, ?_⟩
  rw [← hactual, fromProjectiveState_toProjectiveState
    (unit_active_wall_clock_ne_zero (by rw [hactual]; exact hunit)) hcend]
  exact hflow

end BianchiIX
