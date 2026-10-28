import BianchiIX.Dynamics.PartialCoreDownwardReturn

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

/-- Above the active section, the ordinary first-return germ is already downward oriented. -/
theorem partialCoreDownwardReturn_agrees_eventually {k : ℝ} {y : ProjectiveState}
    (hk : 6 ≤ k) (hy : coreRegion k y) (hR : coreRadius (y 0) (y 2) = k)
    (hV : 1 < y 2) :
    (partialCoreDownwardReturnTime =ᶠ[𝓝 y] partialCoreReturnTime) ∧
      (partialCoreDownwardReturnState =ᶠ[𝓝 y] partialCoreReturnState) := by
  have H := partialCoreReturn_regular hk hy hR hV
  have HD := partialCoreDownwardReturn_regular hk hy hR (Or.inl hV)
  have heq := (partialCoreDownwardReturn_agrees hk hy hR (Or.inl hV)).1
  have hbase := H.2.2.2.self_of_nhds
  have hdom := hbase.1.1.2.1
  have hA := (hbase.2 _ ⟨hbase.1.1.1.le, le_rfl⟩).2
  have hr : normalizedEventRate projectiveActiveWall (fromProjectiveState y) 0
      (partialCoreReturnTime y) < 0 := by
    rw [← heq]
    exact HD.2.2.2.1.self_of_nhds.1.1.2.2.2
  have hD := (coreRegion_clock_regular hk hy).1
  have hc : ContinuousAt (fun z => normalizedEventRate projectiveActiveWall
      (fromProjectiveState z) 0 (partialCoreReturnTime z)) y :=
    ContinuousAt.comp
      (g := fun p : NormalizedState × ℝ => normalizedEventRate projectiveActiveWall p.1 0 p.2)
      (f := fun z => (fromProjectiveState z, partialCoreReturnTime z))
      (continuousAt_activeWall_event_rate hdom hA.ne')
      (((contDiffAt_fromProjectiveState 1 hD.ne').continuousAt).prodMk H.2.1.continuousAt)
  have Hnear : ∀ᶠ z in 𝓝 y, partialCoreDownwardReturnTime z = partialCoreReturnTime z ∧
      partialCoreDownwardReturnState z = partialCoreReturnState z := by
    filter_upwards [H.2.2.2, hc.eventually (gt_mem_nhds hr)] with z hz hneg
    have hfirst : IsLeast {t | 0 < t ∧ t ∈ normalizedMaxDomain (fromProjectiveState z) 0 ∧
        projectiveOriginalFlow z 0 t 2 = 1 ∧
        normalizedEventRate projectiveActiveWall (fromProjectiveState z) 0 t < 0}
        (partialCoreReturnTime z) :=
      ⟨⟨hz.1.1.1, hz.1.1.2.1, hz.1.1.2.2, hneg⟩,
        fun _ ht => hz.1.2 ⟨ht.1, ht.2.1, ht.2.2.1⟩⟩
    have ht := partialCoreDownwardReturnTime_eq hfirst
    exact ⟨ht, by simp only [partialCoreDownwardReturnState, partialCoreReturnState, ht]⟩
  exact ⟨Hnear.mono fun _ h => h.1, Hnear.mono fun _ h => h.2⟩

end BianchiIX
