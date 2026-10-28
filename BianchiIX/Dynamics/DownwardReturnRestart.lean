import BianchiIX.Dynamics.PartialCoreDownwardReturn
import BianchiIX.Dynamics.ProjectiveReflection

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

/-- A finite prefix without a downward crossing leaves the same oriented first return. -/
theorem partialCoreDownwardReturn_restart {y : ProjectiveState} {S T : ℝ}
    (hD : 0 < projectiveStateDenom y) (hS : 0 ≤ S)
    (hA : 0 < 1 + normalizedMaxCurve (fromProjectiveState y) 0 S 0)
    (havoid : ∀ t ∈ Ioc 0 S, projectiveOriginalFlow y 0 t 2 = 1 →
      ¬ normalizedEventRate projectiveActiveWall (fromProjectiveState y) 0 t < 0)
    (HT : IsLeast {t | 0 < t ∧
      t ∈ normalizedMaxDomain (fromProjectiveState (projectiveOriginalFlow y 0 S)) 0 ∧
      projectiveOriginalFlow (projectiveOriginalFlow y 0 S) 0 t 2 = 1 ∧
      normalizedEventRate projectiveActiveWall (fromProjectiveState (projectiveOriginalFlow y 0 S)) 0 t < 0} T) :
    IsLeast {t | 0 < t ∧ t ∈ normalizedMaxDomain (fromProjectiveState y) 0 ∧
      projectiveOriginalFlow y 0 t 2 = 1 ∧
      normalizedEventRate projectiveActiveWall (fromProjectiveState y) 0 t < 0} (S + T) ∧
      partialCoreDownwardReturnTime y = S + T ∧
      partialCoreDownwardReturnState y =
        toCoreAngleState (projectiveOriginalFlow (projectiveOriginalFlow y 0 S) 0 T) := by
  let z := projectiveOriginalFlow y 0 S
  have hc := fromProjectiveState_constraint hD.ne'
  have hdom := normalizedMaxDomain_contains_Ici_of_constraint hc 0 hS
  have hbase : fromProjectiveState z = normalizedMaxCurve (fromProjectiveState y) 0 S :=
    fromProjectiveState_toProjectiveState hA.ne' ((normalizedMaxCurve_constraint hdom).trans hc)
  have hcz : stateConstraint (fromProjectiveState z) = 1 := by
    rw [hbase]
    exact (normalizedMaxCurve_constraint hdom).trans hc
  have Hflow (t : ℝ) (ht : 0 ≤ t) :
      normalizedMaxCurve (fromProjectiveState z) 0 t =
        normalizedMaxCurve (fromProjectiveState y) 0 (S + t) := by
    rw [hbase]
    have H := normalizedMaxCurve_shift (by simpa only [zero_add] using hdom)
      (normalizedMaxDomain_contains_Ici_of_constraint hc 0 (add_nonneg ht hS))
    simpa only [zero_add, add_comm t S] using H
  have Hproj (t : ℝ) (ht : 0 ≤ t) :
      projectiveOriginalFlow z 0 t = projectiveOriginalFlow y 0 (S + t) :=
    congrArg toProjectiveState (Hflow t ht)
  have Hrate (t : ℝ) (ht : 0 ≤ t) :
      normalizedEventRate projectiveActiveWall (fromProjectiveState z) 0 t =
        normalizedEventRate projectiveActiveWall (fromProjectiveState y) 0 (S + t) := by
    unfold normalizedEventRate
    rw [Hflow t ht]
  have hT : 0 < T := HT.1.1
  have Hleast : IsLeast {t | 0 < t ∧ t ∈ normalizedMaxDomain (fromProjectiveState y) 0 ∧
      projectiveOriginalFlow y 0 t 2 = 1 ∧
      normalizedEventRate projectiveActiveWall (fromProjectiveState y) 0 t < 0} (S + T) := by
    refine ⟨⟨add_pos_of_nonneg_of_pos hS hT,
      normalizedMaxDomain_contains_Ici_of_constraint hc 0 (add_nonneg hS hT.le), ?_, ?_⟩, ?_⟩
    · rw [← Hproj T hT.le]
      exact HT.1.2.2.1
    · rw [← Hrate T hT.le]
      exact HT.1.2.2.2
    · intro t ht
      by_cases htS : t ≤ S
      · exact (havoid t ⟨ht.1, htS⟩ ht.2.2.1 ht.2.2.2).elim
      · have hsub : 0 < t - S := sub_pos.mpr (lt_of_not_ge htS)
        have HP := Hproj (t - S) hsub.le
        have HR := Hrate (t - S) hsub.le
        rw [add_sub_cancel] at HP HR
        have H := HT.2 ⟨hsub, normalizedMaxDomain_contains_Ici_of_constraint hcz 0 hsub.le,
          by rw [HP]; exact ht.2.2.1, by rw [HR]; exact ht.2.2.2⟩
        linarith only [H]
  have Htime := partialCoreDownwardReturnTime_eq Hleast
  refine ⟨Hleast, Htime, ?_⟩
  unfold partialCoreDownwardReturnState
  rw [Htime, ← Hproj T hT.le]

/-- Strict avoidance on a compact prefix persists in the full ordinary projective neighborhood. -/
theorem eventually_projectiveOriginalFlow_below_section {y : ProjectiveState} {S : ℝ}
    (hD : 0 < projectiveStateDenom y)
    (hreg : ∀ t ∈ Icc 0 S, t ∈ normalizedMaxDomain (fromProjectiveState y) 0 ∧
      0 < 1 + normalizedMaxCurve (fromProjectiveState y) 0 t 0 ∧
      projectiveOriginalFlow y 0 t 2 < 1) :
    ∀ᶠ z in 𝓝 y, ∀ t ∈ Icc 0 S,
      0 < 1 + normalizedMaxCurve (fromProjectiveState z) 0 t 0 ∧
        projectiveOriginalFlow z 0 t 2 < 1 := by
  apply isCompact_Icc.eventually_forall_of_forall_eventually
  intro t ht
  obtain ⟨hdom, hA, hv⟩ := hreg t ht
  have hpair : ContinuousAt (fun p : ProjectiveState × ℝ => (fromProjectiveState p.1, p.2)) (y, t) := by
    exact ((contDiffAt_fromProjectiveState 1 hD.ne').continuousAt.comp
      (continuousAt_fst : ContinuousAt (Prod.fst : ProjectiveState × ℝ → ProjectiveState) (y, t))).prodMk continuousAt_snd
  have hflow : ContinuousAt (fun p : ProjectiveState × ℝ =>
      normalizedMaxCurve (fromProjectiveState p.1) 0 p.2) (y, t) :=
    ContinuousAt.comp (g := fun p : NormalizedState × ℝ => normalizedMaxCurve p.1 0 p.2)
      (f := fun p : ProjectiveState × ℝ => (fromProjectiveState p.1, p.2))
      (normalizedMaxCurve_regular hdom).2.continuousAt hpair
  have hclock : ContinuousAt (fun p : ProjectiveState × ℝ =>
      1 + normalizedMaxCurve (fromProjectiveState p.1) 0 p.2 0) (y, t) :=
    continuousAt_const.add (continuousAt_pi.mp hflow 0)
  have hproj : ContinuousAt (fun p : ProjectiveState × ℝ => projectiveOriginalFlow p.1 0 p.2) (y, t) :=
    ContinuousAt.comp (g := toProjectiveState)
      (f := fun p : ProjectiveState × ℝ => normalizedMaxCurve (fromProjectiveState p.1) 0 p.2)
      (contDiffAt_toProjectiveState 1 hA.ne').continuousAt hflow
  exact (hclock.eventually (lt_mem_nhds hA)).and
    ((continuousAt_pi.mp hproj 2).eventually (gt_mem_nhds hv))

/-- Canonical return times and states agree as ordinary germs after a strict below-section prefix. -/
theorem partialCoreDownwardReturn_restart_eventuallyEq {y : ProjectiveState} {S : ℝ}
    (hD : 0 < projectiveStateDenom y) (hS : 0 ≤ S)
    (hreg : ∀ t ∈ Icc 0 S, t ∈ normalizedMaxDomain (fromProjectiveState y) 0 ∧
      0 < 1 + normalizedMaxCurve (fromProjectiveState y) 0 t 0 ∧
      projectiveOriginalFlow y 0 t 2 < 1)
    (Hnear : ∀ᶠ z in 𝓝 (projectiveOriginalFlow y 0 S),
      IsLeast {t | 0 < t ∧ t ∈ normalizedMaxDomain (fromProjectiveState z) 0 ∧
        projectiveOriginalFlow z 0 t 2 = 1 ∧
        normalizedEventRate projectiveActiveWall (fromProjectiveState z) 0 t < 0}
        (partialCoreDownwardReturnTime z)) :
    (partialCoreDownwardReturnTime =ᶠ[𝓝 y]
      fun z => S + partialCoreDownwardReturnTime (projectiveOriginalFlow z 0 S)) ∧
    (partialCoreDownwardReturnState =ᶠ[𝓝 y]
      fun z => partialCoreDownwardReturnState (projectiveOriginalFlow z 0 S)) := by
  have hc := (hasFDerivAt_projectiveOriginalFlow_initial hD
    (hreg S ⟨hS, le_rfl⟩).1 (hreg S ⟨hS, le_rfl⟩).2.1).continuousAt
  have H : ∀ᶠ z in 𝓝 y,
      partialCoreDownwardReturnTime z = S + partialCoreDownwardReturnTime (projectiveOriginalFlow z 0 S) ∧
      partialCoreDownwardReturnState z = partialCoreDownwardReturnState (projectiveOriginalFlow z 0 S) := by
    filter_upwards [continuous_projectiveStateDenom.continuousAt.eventually (lt_mem_nhds hD),
      eventually_projectiveOriginalFlow_below_section hD hreg, hc.tendsto.eventually Hnear] with z hd hz hn
    exact (partialCoreDownwardReturn_restart hd hS (hz S ⟨hS, le_rfl⟩).1
      (fun t ht hhit => by
        have hv := (hz t ⟨ht.1.le, ht.2⟩).2
        rw [hhit] at hv
        exact (lt_irrefl _ hv).elim) hn).2
  exact ⟨H.mono fun _ h => h.1, H.mono fun _ h => h.2⟩

end BianchiIX
