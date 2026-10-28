import BianchiIX.Dynamics.MainWallArrival
import Mathlib.Topology.Compactness.Lindelof

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

def mainWallArrivalRelation (h k t₀ : ℝ) : Set (SectionCoordinates × ℝ) :=
  {z | z.1 ∈ mainWallChartDomain h ∧ z.2 ∈ normalizedMaxDomain (mainWallChart h z.1) t₀ ∧
    normalizedMaxCurve (mainWallChart h z.1) t₀ z.2 2 = k ∧
    normalizedMaxCurve (mainWallChart h z.1) t₀ z.2 0 < 0}

def MainWallArrival.empty (h k t₀ : ℝ) : MainWallArrival h k t₀ where
  source := ∅
  time := fun _ => t₀
  map := id
  isOpen_source := isOpen_empty
  source_chart := empty_subset _
  target_chart := fun _ hy => hy.elim
  time_mem := fun _ hy => hy.elim
  time_regular := fun _ hy => hy.elim
  map_regular := fun _ hy => hy.elim
  arrival := fun _ hy => hy.elim
  injOn := injOn_empty _

/-- Countably many actual local arrivals cover all signed crossing times. -/
structure MainWallArrivalAtlas (h k t₀ : ℝ) where
  branch : ℕ → MainWallArrival h k t₀
  covers : ∀ z ∈ mainWallArrivalRelation h k t₀,
    ∃ n, z.1 ∈ (branch n).source ∧ (branch n).time (mainWallChart h z.1) = z.2

theorem exists_mainWallArrivalAtlas {h k t₀ : ℝ} (hh : 0 < h) (hk : 0 < k) :
    Nonempty (MainWallArrivalAtlas h k t₀) := by
  classical
  let Z := mainWallArrivalRelation h k t₀
  by_cases hZ : Z.Nonempty
  · let : Nonempty Z := hZ.to_subtype
    have hpatch (z : Z) : ∃ (P : MainWallArrival h k t₀) (V : Set (SectionCoordinates × ℝ)),
        IsOpen V ∧ z.val ∈ V ∧ ∀ q ∈ V, q.1 ∈ P.source ∧
          q.2 ∈ normalizedMaxDomain (mainWallChart h q.1) t₀ ∧
          (normalizedMaxCurve (mainWallChart h q.1) t₀ q.2 2 = k ↔
            P.time (mainWallChart h q.1) = q.2) := by
      obtain ⟨P, _, _, _, huniq⟩ := exists_mainWallArrival hh hk
        z.property.1 z.property.2.1 z.property.2.2.1 z.property.2.2.2
      obtain ⟨V, hV, hVopen, hzV⟩ := mem_nhds_iff.mp huniq
      exact ⟨P, V, hVopen, hzV, hV⟩
    choose P V hVopen hzV hV using hpatch
    obtain ⟨f, hf⟩ := (HereditarilyLindelofSpace.isLindelof Z).indexed_countable_subcover V hVopen
      (by intro z hz; exact mem_iUnion.mpr ⟨⟨z, hz⟩, hzV ⟨z, hz⟩⟩)
    refine ⟨{ branch := fun n => P (f n), covers := ?_ }⟩
    intro z hz
    obtain ⟨n, hn⟩ := mem_iUnion.mp (hf hz)
    have H := hV (f n) z hn
    exact ⟨n, H.1, H.2.2.mp hz.2.2.1⟩
  · exact ⟨{ branch := fun _ => MainWallArrival.empty h k t₀,
             covers := fun z hz => (hZ ⟨z, hz⟩).elim }⟩

namespace MainWallArrival

variable {h k t₀ : ℝ} (P : MainWallArrival h k t₀)

def coordinateTime (y : SectionCoordinates) : ℝ := P.time (mainWallChart h y)

theorem continuousOn_coordinateTime : ContinuousOn P.coordinateTime P.source :=
  fun y hy => ((P.time_regular y hy).continuousAt.comp
    (contDiffAt_mainWallChart (P.source_chart hy) 1).continuousAt).continuousWithinAt

theorem map_eq_coordinates {y : SectionCoordinates} (hy : y ∈ P.source) :
    P.map y = mainWallCoordinates (normalizedMaxCurve (mainWallChart h y) t₀ (P.coordinateTime y)) := by
  rw [coordinateTime, ← P.arrival y hy, mainWallCoordinates_chart]

theorem mem_relation {y : SectionCoordinates} (hy : y ∈ P.source) :
    (y, P.coordinateTime y) ∈ mainWallArrivalRelation h k t₀ := by
  refine ⟨P.source_chart hy, P.time_mem y hy, ?_, ?_⟩
  · exact (congrArg (fun x : NormalizedState => x 2) (P.arrival y hy)).symm
  · rw [coordinateTime, ← P.arrival y hy]
    exact mainWallChart_negative (P.target_chart hy)

end MainWallArrival

theorem MainWallArrivalAtlas.mem_relation_iff {h k t₀ : ℝ} (C : MainWallArrivalAtlas h k t₀)
    (y : SectionCoordinates) (t : ℝ) :
    (y, t) ∈ mainWallArrivalRelation h k t₀ ↔
      ∃ n, y ∈ (C.branch n).source ∧ (C.branch n).coordinateTime y = t := by
  constructor
  · exact C.covers (y, t)
  · rintro ⟨n, hy, ht⟩
    rw [← ht]
    exact (C.branch n).mem_relation hy

end BianchiIX
