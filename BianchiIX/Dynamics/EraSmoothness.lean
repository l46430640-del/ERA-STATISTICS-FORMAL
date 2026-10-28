import BianchiIX.Analysis.ImplicitBranch
import BianchiIX.Dynamics.EraEventTimes
import BianchiIX.Dynamics.EraTimeRegularity
import BianchiIX.Dynamics.FlowSmoothRegularity

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology ContDiff

/-- The terminal event and the complete era have the same normalized endpoint. -/
theorem EraEventItinerary.terminal_endpoint {η : ℝ} {J m : ℕ} {X : CoreAngleState}
    (H : EraEventItinerary η J m X) :
    0 < eraReturnTime η J m X ∧
      eraReturnTime η J m X ∈ normalizedMaxDomain (fromProjectiveState (coreRadiusEntry X)) 0 ∧
      normalizedMaxCurve (axisCycle (fromProjectiveState (coreTailEntry (eraCoreExit m X)))) 0
        (terminalNaturalTime η J (eraCoreExit m X)) =
        (axisFrame (eraReturnFrame m)).map (normalizedMaxCurve
          (fromProjectiveState (coreRadiusEntry X)) 0 (eraReturnTime η J m X)) := by
  obtain ⟨hT, ht, hend⟩ := eraReturn_normalized_endpoint
    (fun j hj => (H.core j hj).2.2.1)
    (fun j hj => ⟨H.reflection_time_pos j hj, by
      simpa only [Function.iterate_succ_apply'] using (H.reflection j hj).2.2.2⟩)
    (H.core m le_rfl).2.2.2 H.terminal.2.1.1.1 H.terminal.2.2.1 H.terminal.2.2.2.1
  have hcore := H.core_endpoints m le_rfl
  have hS : 0 ≤ coreExitTime m X := hcore.1.trans (H.event_time_order.1 m le_rfl).le
  have hc : stateConstraint (fromProjectiveState (coreRadiusEntry X)) = 1 :=
    fromProjectiveState_constraint (coreRadiusReturnValid_denom_pos (H.core 0 (Nat.zero_le _)).2.2.1).ne'
  have hcstart : stateConstraint (axisCycle (fromProjectiveState (coreTailEntry (eraCoreExit m X)))) = 1 := by
    rw [axisCycle_constraint, hcore.2.2, (axisFrame (corePrefixFrame m)).constraint]
    exact (normalizedMaxCurve_forward_of_constraint hc hS).2.1
  have hunit : toProjectiveState (normalizedMaxCurve
      (axisCycle (fromProjectiveState (coreTailEntry (eraCoreExit m X)))) 0
      (terminalNaturalTime η J (eraCoreExit m X))) 2 = 1 := by
    rw [H.terminal.2.2.1]
    exact H.terminal.2.2.2.1
  have hrec := fromProjectiveState_toProjectiveState (unit_active_wall_clock_ne_zero hunit)
    ((normalizedMaxCurve_forward_of_constraint hcstart H.terminal.2.1.1.1.le).2.1)
  rw [H.terminal.2.2.1] at hrec
  exact ⟨hT, ht, hrec.symm.trans hend⟩

/-- One final transverse equation upgrades the whole finite itinerary, without higher passage estimates. -/
theorem eraReturn_contDiff_smooth {η : ℝ} {J m : ℕ} {X : CoreAngleState}
    (hcτ : ContinuousAt (eraReturnTime η J m) X)
    (hnear : ∀ᶠ Y in 𝓝 X, EraEventItinerary η J m Y) :
    ContDiffAt ℝ ∞ (eraReturnTime η J m) X ∧
      ContDiffAt ℝ ∞ (eraOutputState η J m) X ∧
      ContDiffAt ℝ ∞ (eraNextState η J m) X := by
  let τ := eraReturnTime η J m
  let e : CoreAngleState → NormalizedState := fun Y => fromProjectiveState (coreRadiusEntry Y)
  let A := axisFrame (eraReturnFrame m)
  let F : CoreAngleState × ℝ → NormalizedState := fun z => A.map (normalizedMaxCurve (e z.1) 0 z.2)
  let Q : CoreAngleState × ℝ → ℝ := fun z => projectiveActiveWall (F z)
  have H := hnear.self_of_nhds
  have hEnd := H.terminal_endpoint
  have hlevel : ∀ᶠ Y in 𝓝 X, Q (Y, τ Y) = 1 := by
    filter_upwards [hnear] with Y HY
    change projectiveActiveWall (A.map (normalizedMaxCurve (e Y) 0 (τ Y))) = 1
    rw [← HY.terminal_endpoint.2.2]
    exact HY.terminal.2.1.1.2.2
  have hA : 1 + F (X, τ X) 0 ≠ 0 := unit_active_wall_clock_ne_zero hlevel.self_of_nhds
  have he : ContDiffAt ℝ ∞ e X :=
    (contDiffAt_fromProjectiveState ∞
      (coreRadiusReturnValid_denom_pos (H.core 0 (Nat.zero_le _)).2.2.1).ne').comp X
      (contDiffAt_coreRadiusEntry ∞ (by simpa using (lt_trans (by norm_num : (1 : ℝ) < 2)
        (H.core 0 (Nat.zero_le _)).1)))
  have hF : ContDiffAt ℝ ∞ F (X, τ X) := A.map.contDiff.contDiffAt.comp (X, τ X)
    ((contDiffAt_normalizedMaxCurve_smooth hEnd.2.1).comp (X, τ X)
      ((he.comp (X, τ X) contDiffAt_fst).prodMk contDiffAt_snd))
  have hw := contDiffAt_projectiveActiveWall ∞ hA
  have hQ : ContDiffAt ℝ ∞ Q (X, τ X) := hw.comp (X, τ X) hF
  have ht : HasDerivAt (fun t => F (X, t)) (normalizedField (F (X, τ X))) (τ X) := by
    change HasDerivAt (fun t => A.map (normalizedMaxCurve (e X) 0 t))
      (normalizedField (A.map (normalizedMaxCurve (e X) 0 (τ X)))) (τ X)
    rw [A.field]
    exact A.map.hasFDerivAt.comp_hasDerivAt (τ X) (hasDerivAt_normalizedMaxCurve hEnd.2.1)
  have htrans : fderiv ℝ projectiveActiveWall (F (X, τ X))
      (normalizedField (F (X, τ X))) ≠ 0 := by
    change fderiv ℝ projectiveActiveWall (A.map _) (normalizedField (A.map _)) ≠ 0
    rw [← hEnd.2.2]
    exact ne_of_gt H.terminal.2.2.2.2
  have htime : HasDerivAt (fun t => Q (X, t))
      (fderiv ℝ projectiveActiveWall (F (X, τ X)) (normalizedField (F (X, τ X)))) (τ X) := by
    have hd : HasFDerivAt projectiveActiveWall (fderiv ℝ projectiveActiveWall (F (X, τ X)))
        (F (X, τ X)) := (hw.differentiableAt (by simp)).hasFDerivAt
    exact hd.comp_hasDerivAt (τ X) ht
  have hτ : ContDiffAt ℝ ∞ τ X := contDiffAt_scalar_event_branch (by simp) hQ
    htime htrans rfl hcτ
    (hlevel.mono fun _ h => h.trans hlevel.self_of_nhds.symm)
  have hFull : ContDiffAt ℝ ∞ (fun Y => F (Y, τ Y)) X :=
    hF.comp X (g := F) (f := fun Y => (Y, τ Y)) (contDiffAt_id.prodMk hτ)
  have hstate : eraOutputState η J m =ᶠ[𝓝 X] (fun Y => toProjectiveState (F (Y, τ Y))) := by
    filter_upwards [hnear] with Y HY
    change terminalNaturalState η J (eraCoreExit m Y) = toProjectiveState (A.map _)
    rw [← HY.terminal_endpoint.2.2]
    exact HY.terminal.2.2.1.symm
  have hS : ContDiffAt ℝ ∞ (eraOutputState η J m) X :=
    ((contDiffAt_toProjectiveState ∞ hA).comp X (g := toProjectiveState)
      (f := fun Y => F (Y, τ Y)) hFull).congr_of_eventuallyEq hstate
  have hr : ContDiffAt ℝ ∞ (eraOutputRadius η J m) X :=
    (contDiffAt_projectiveCoreRadius ∞ (by
      change 0 < terminalNaturalState η J (eraCoreExit m X) 2
      rw [H.terminal.2.2.2.1]
      norm_num)).comp X hS
  refine ⟨hτ, hS, ?_⟩
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i
  · exact hr
  · exact contDiffAt_pi.mp hS 1
  · exact contDiffAt_pi.mp hS 3

end BianchiIX
