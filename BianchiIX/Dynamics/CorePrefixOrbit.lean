import BianchiIX.Dynamics.CoreSectionPhysical
import BianchiIX.Dynamics.AxisFrameComposition

noncomputable section

namespace BianchiIX

/-- Original time spent in the first `m` nonterminal core-reflection passages. -/
def corePrefixTime (m : ℕ) (X : CoreAngleState) : ℝ :=
  ∑ j ∈ Finset.range m, coreReflectionTime ((coreReflectionState coreRadiusReturnTime)^[j] X)

def corePrefixFrame : ℕ → Fin 6
  | 0 => 0
  | m + 1 => (axisFrame_comp 3 (corePrefixFrame m)).choose

theorem corePrefixFrame_succ (m : ℕ) (x : NormalizedState) :
    (axisFrame (corePrefixFrame (m + 1))).map x = axisSwap ((axisFrame (corePrefixFrame m)).map x) :=
  ((axisFrame_comp 3 (corePrefixFrame m)).choose_spec x).symm

theorem corePrefixTime_succ (m : ℕ) (X : CoreAngleState) :
    corePrefixTime (m + 1) X = coreReflectionTime ((coreReflectionState coreRadiusReturnTime)^[m] X) +
      corePrefixTime m X := by
  rw [corePrefixTime, Finset.sum_range_succ]
  exact add_comm _ _

/-- Each finite reflected itinerary is one exact flow segment with its accumulated physical time and axis frame. -/
theorem corePrefix_normalized_endpoint {m : ℕ} {X : CoreAngleState}
    (Hvalid : ∀ j ≤ m, coreRadiusReturnValid ((coreReflectionState coreRadiusReturnTime)^[j] X))
    (Hconn : ∀ j < m,
      let Y := (coreReflectionState coreRadiusReturnTime)^[j] X
      0 < coreReflectionTime Y ∧
        coreRadiusEntry (coreReflectionState coreRadiusReturnTime Y) = projectiveReflection
          (projectiveOriginalFlow (coreRadiusEntry Y) 0 (coreReflectionTime Y))) :
    0 ≤ corePrefixTime m X ∧
      fromProjectiveState (coreRadiusEntry ((coreReflectionState coreRadiusReturnTime)^[m] X)) =
        (axisFrame (corePrefixFrame m)).map
          (normalizedMaxCurve (fromProjectiveState (coreRadiusEntry X)) 0 (corePrefixTime m X)) := by
  let x := fromProjectiveState (coreRadiusEntry X)
  have hc : stateConstraint x = 1 :=
    fromProjectiveState_constraint (coreRadiusReturnValid_denom_pos (Hvalid 0 (Nat.zero_le _))).ne'
  induction m with
  | zero =>
    simp only [corePrefixTime, Finset.range_zero, Finset.sum_empty, Function.iterate_zero_apply,
      corePrefixFrame, normalizedMaxCurve_initial]
    exact ⟨le_rfl, rfl⟩
  | succ m ih =>
    obtain ⟨hT, hend⟩ := ih (fun j hj => Hvalid j (by omega)) (fun j hj => Hconn j (by omega))
    obtain ⟨ht, hlocal⟩ := Hconn m (by omega)
    have hcT : stateConstraint (normalizedMaxCurve x 0 (corePrefixTime m X)) = 1 :=
      (normalizedMaxCurve_forward_of_constraint hc hT).2.1
    have hshift := normalizedMaxCurve_shift (t₀ := (0 : ℝ))
      (t := coreReflectionTime ((coreReflectionState coreRadiusReturnTime)^[m] X))
      (by simpa only [zero_add] using normalizedMaxDomain_contains_Ici_of_constraint hc 0 hT)
      (normalizedMaxDomain_contains_Ici_of_constraint hc 0 (add_nonneg ht.le hT))
    simp only [zero_add] at hshift
    refine ⟨by rw [corePrefixTime_succ]; exact add_nonneg ht.le hT, ?_⟩
    rw [Function.iterate_succ_apply',
      coreReflection_normalized_endpoint (Hvalid m (by omega)) ht hlocal, hend,
      (axisFrame (corePrefixFrame m)).maxCurve
        (normalizedMaxDomain_contains_Ici_of_constraint hcT 0 ht.le),
      hshift, corePrefixTime_succ, corePrefixFrame_succ]

end BianchiIX
