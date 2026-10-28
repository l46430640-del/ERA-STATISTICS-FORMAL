import BianchiIX.Dynamics.EntrancePartialCoreEntry
import BianchiIX.Dynamics.PartialCoreDownwardReturn
import BianchiIX.Dynamics.ProjectiveReflection

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

/-- A positive-rate entrance creates no downward event, so the next downward time adds exactly. -/
theorem entranceReturn_downward_restart {y : ProjectiveState} {T : ℝ}
    (hD : 0 < projectiveStateDenom y) (HE : entranceReturnValid y)
    (HT : IsLeast {t | 0 < t ∧ t ∈ normalizedMaxDomain (fromProjectiveState (entranceReturnState y)) 0 ∧
      projectiveOriginalFlow (entranceReturnState y) 0 t 2 = 1 ∧
      normalizedEventRate projectiveActiveWall (fromProjectiveState (entranceReturnState y)) 0 t < 0} T) :
    IsLeast {t | 0 < t ∧ t ∈ normalizedMaxDomain (fromProjectiveState y) 0 ∧
      projectiveOriginalFlow y 0 t 2 = 1 ∧ normalizedEventRate projectiveActiveWall (fromProjectiveState y) 0 t < 0}
        (entranceReturnTime y + T) ∧
    partialCoreDownwardReturnTime y = entranceReturnTime y + T ∧
    partialCoreDownwardReturnState y = toCoreAngleState (projectiveOriginalFlow (entranceReturnState y) 0 T) := by
  let S := entranceReturnTime y
  let z := entranceReturnState y
  have hS : 0 < S := HE.1.1.1
  have hT : 0 < T := HT.1.1
  have hA := (HE.2.1 S ⟨hS.le, le_rfl⟩).2
  have hc := fromProjectiveState_constraint hD.ne'
  have hdom := normalizedMaxDomain_contains_Ici_of_constraint hc 0 hS.le
  have hbase : fromProjectiveState z = normalizedMaxCurve (fromProjectiveState y) 0 S :=
    fromProjectiveState_toProjectiveState hA.ne' ((normalizedMaxCurve_constraint hdom).trans hc)
  have hcz : stateConstraint (fromProjectiveState z) = 1 := by
    rw [hbase]
    exact (normalizedMaxCurve_constraint hdom).trans hc
  have Hflow (t : ℝ) (ht : 0 ≤ t) :
      normalizedMaxCurve (fromProjectiveState z) 0 t = normalizedMaxCurve (fromProjectiveState y) 0 (S + t) := by
    rw [hbase]
    have H := normalizedMaxCurve_shift (by simpa only [zero_add] using hdom)
      (normalizedMaxDomain_contains_Ici_of_constraint hc 0 (add_nonneg ht hS.le))
    simpa only [zero_add, add_comm t S] using H
  have Hproj (t : ℝ) (ht : 0 ≤ t) : projectiveOriginalFlow z 0 t = projectiveOriginalFlow y 0 (S + t) :=
    congrArg toProjectiveState (Hflow t ht)
  have Hrate (t : ℝ) (ht : 0 ≤ t) :
      normalizedEventRate projectiveActiveWall (fromProjectiveState z) 0 t =
        normalizedEventRate projectiveActiveWall (fromProjectiveState y) 0 (S + t) := by
    unfold normalizedEventRate
    rw [Hflow t ht]
  have Hleast : IsLeast {t | 0 < t ∧ t ∈ normalizedMaxDomain (fromProjectiveState y) 0 ∧
      projectiveOriginalFlow y 0 t 2 = 1 ∧ normalizedEventRate projectiveActiveWall (fromProjectiveState y) 0 t < 0}
        (S + T) := by
    refine ⟨⟨add_pos hS hT, normalizedMaxDomain_contains_Ici_of_constraint hc 0 (add_pos hS hT).le, ?_, ?_⟩, ?_⟩
    · rw [← Hproj T hT.le]
      exact HT.1.2.2.1
    · rw [← Hrate T hT.le]
      exact HT.1.2.2.2
    · intro t ht
      by_cases htS : t ≤ S
      · have H := HE.2.2.2 t ⟨ht.1.le, htS⟩
        linarith only [H, ht.2.2.2]
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

/-- The same canonical downward event is C2 below the core after composing with the upward entrance. -/
theorem entrancePartialCore_downward_regular {y : ProjectiveState} {η : ℝ}
    (hk : 8 ≤ coreRadius (y 0) (y 2)) (hm : 1 ≤ y 0)
    (hu : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000) (hv : 0 < y 2 ∧ y 2 < 1)
    (hw : 0 ≤ y 3 ∧ y 3 ≤ 1 / 10000) (hη : 0 < η ∧ η ≤ 1 / 10000)
    (hsmall : y 1 + y 2 * y 3 ≤ η / (2 * coreRadius (y 0) (y 2))) :
    let z := entranceReturnState y
    IsLeast {t | 0 < t ∧ t ∈ normalizedMaxDomain (fromProjectiveState y) 0 ∧
      projectiveOriginalFlow y 0 t 2 = 1 ∧ normalizedEventRate projectiveActiveWall (fromProjectiveState y) 0 t < 0}
        (partialCoreDownwardReturnTime y) ∧
      partialCoreDownwardReturnTime y = entranceReturnTime y + partialCoreDownwardReturnTime z ∧
      partialCoreDownwardReturnState y = partialCoreDownwardReturnState z ∧
      ContDiffAt ℝ 2 partialCoreDownwardReturnTime y ∧ ContDiffAt ℝ 2 partialCoreDownwardReturnState y ∧
      (partialCoreDownwardReturnTime =ᶠ[𝓝 y] fun w => entranceReturnTime w + partialCoreDownwardReturnTime (entranceReturnState w)) ∧
      (partialCoreDownwardReturnState =ᶠ[𝓝 y] fun w => partialCoreDownwardReturnState (entranceReturnState w)) := by
  intro z
  have hk' : 7 / 4 ≤ coreRadius (y 0) (y 2) := by linarith only [hk]
  have HE := entranceReturn_regular hk' hm hu hv hw
  obtain ⟨hκ, _, hhit, hmz, hregion, _⟩ := entranceReturn_partialCore_entry hk hm hu hv hw hη hsmall
  have HC := partialCoreDownwardReturn_regular hκ hregion rfl (Or.inr ⟨hhit, hmz.le⟩)
  have hD := entrance_initial_denom_pos hk' hm hu hv hw
  have hDc : Continuous projectiveStateDenom := by unfold projectiveStateDenom projectiveDenom curvature; fun_prop
  have Hnear := HE.2.2.1.continuousAt.tendsto.eventually HC.2.2.2.1
  have Hboth : ∀ᶠ w in 𝓝 y,
      partialCoreDownwardReturnTime w = entranceReturnTime w + partialCoreDownwardReturnTime (entranceReturnState w) ∧
      partialCoreDownwardReturnState w = partialCoreDownwardReturnState (entranceReturnState w) := by
    filter_upwards [hDc.continuousAt.eventually (lt_mem_nhds hD), HE.2.2.2.2.2, Hnear] with w hd he hc
    exact (entranceReturn_downward_restart hd he hc.1).2
  have Htime := Hboth.mono fun _ h => h.1
  have Hstate := Hboth.mono fun _ h => h.2
  have Hbase := entranceReturn_downward_restart hD HE.1 HC.2.2.2.1.self_of_nhds.1
  have ht : ContDiffAt ℝ 2 partialCoreDownwardReturnTime y :=
    (HE.2.1.add (ContDiffAt.comp (g := partialCoreDownwardReturnTime) y HC.2.1 HE.2.2.1)).congr_of_eventuallyEq Htime
  have hz : ContDiffAt ℝ 2 partialCoreDownwardReturnState y :=
    (ContDiffAt.comp (g := partialCoreDownwardReturnState) y HC.2.2.1 HE.2.2.1).congr_of_eventuallyEq Hstate
  refine ⟨?_, Htime.self_of_nhds, Hstate.self_of_nhds, ht, hz, Htime, Hstate⟩
  rw [Htime.self_of_nhds]
  exact Hbase.1

end BianchiIX
