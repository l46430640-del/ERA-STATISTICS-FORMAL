import BianchiIX.Dynamics.AxisArrival
import Mathlib.Topology.Compactness.Lindelof

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

def axisWallArrivalRelation (A B : NormalizedSymmetry) (h k t₀ : ℝ) : Set (SectionCoordinates × ℝ) :=
  {z | z.1 ∈ mainWallChartDomain h ∧ z.2 ∈ normalizedMaxDomain (axisWallChart A h z.1) t₀ ∧
    B.map (normalizedMaxCurve (axisWallChart A h z.1) t₀ z.2) 2 = k ∧
    B.map (normalizedMaxCurve (axisWallChart A h z.1) t₀ z.2) 0 < 0}

def AxisWallArrival.empty (A B : NormalizedSymmetry) (h k t₀ : ℝ) : AxisWallArrival A B h k t₀ where
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

/-- The countable branches cover the actual crossing relation, including every admissible time. -/
structure AxisWallArrivalAtlas (A B : NormalizedSymmetry) (h k t₀ : ℝ) where
  branch : ℕ → AxisWallArrival A B h k t₀
  covers : ∀ z ∈ axisWallArrivalRelation A B h k t₀,
    ∃ n, z.1 ∈ (branch n).source ∧ (branch n).time (axisWallChart A h z.1) = z.2

theorem exists_axisWallArrivalAtlas (A B : NormalizedSymmetry) {h k t₀ : ℝ}
    (hh : 0 < h) (hk : 0 < k) : Nonempty (AxisWallArrivalAtlas A B h k t₀) := by
  classical
  let Z := axisWallArrivalRelation A B h k t₀
  by_cases hZ : Z.Nonempty
  · let : Nonempty Z := hZ.to_subtype
    have hpatch (z : Z) : ∃ (P : AxisWallArrival A B h k t₀) (V : Set (SectionCoordinates × ℝ)),
        IsOpen V ∧ z.val ∈ V ∧ ∀ q ∈ V, q.1 ∈ P.source ∧
          q.2 ∈ normalizedMaxDomain (axisWallChart A h q.1) t₀ ∧
          (B.map (normalizedMaxCurve (axisWallChart A h q.1) t₀ q.2) 2 = k ↔
            P.time (axisWallChart A h q.1) = q.2) := by
      obtain ⟨P, _, _, _, huniq⟩ := exists_axisWallArrival A B hh hk
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
  · exact ⟨{ branch := fun _ => AxisWallArrival.empty A B h k t₀,
             covers := fun z hz => (hZ ⟨z, hz⟩).elim }⟩

namespace AxisWallArrival

variable {A B : NormalizedSymmetry} {h k t₀ : ℝ} (P : AxisWallArrival A B h k t₀)

def coordinateTime (y : SectionCoordinates) : ℝ := P.time (axisWallChart A h y)

theorem continuousOn_coordinateTime : ContinuousOn P.coordinateTime P.source :=
  fun y hy => ((P.time_regular y hy).continuousAt.comp
    (contDiffAt_axisWallChart A (P.source_chart hy) 1).continuousAt).continuousWithinAt

theorem map_eq_coordinates {y : SectionCoordinates} (hy : y ∈ P.source) :
    P.map y = axisWallCoordinates B (normalizedMaxCurve (axisWallChart A h y) t₀ (P.coordinateTime y)) := by
  rw [coordinateTime, ← P.arrival y hy, axisWallCoordinates_chart]

theorem mem_relation {y : SectionCoordinates} (hy : y ∈ P.source) :
    (y, P.coordinateTime y) ∈ axisWallArrivalRelation A B h k t₀ := by
  refine ⟨P.source_chart hy, P.time_mem y hy, ?_, ?_⟩
  · rw [coordinateTime, ← P.arrival y hy, axisWallChart, ContinuousLinearEquiv.apply_symm_apply]
    rfl
  · rw [coordinateTime, ← P.arrival y hy, axisWallChart, ContinuousLinearEquiv.apply_symm_apply]
    exact mainWallChart_negative (P.target_chart hy)

end AxisWallArrival

theorem AxisWallArrivalAtlas.mem_relation_iff {A B : NormalizedSymmetry} {h k t₀ : ℝ}
    (C : AxisWallArrivalAtlas A B h k t₀) (y : SectionCoordinates) (t : ℝ) :
    (y, t) ∈ axisWallArrivalRelation A B h k t₀ ↔
      ∃ n, y ∈ (C.branch n).source ∧ (C.branch n).coordinateTime y = t := by
  constructor
  · exact C.covers (y, t)
  · rintro ⟨n, hy, ht⟩
    rw [← ht]
    exact (C.branch n).mem_relation hy

abbrev AxisWallAtlasFamily {ι : Type*} (A : NormalizedSymmetry) (B : ι → NormalizedSymmetry)
    (h : ℝ) (k : ι → ℝ) (t₀ : ℝ) := ∀ i, AxisWallArrivalAtlas A (B i) h (k i) t₀

theorem exists_axisWallAtlasFamily {ι : Type*} (A : NormalizedSymmetry) (B : ι → NormalizedSymmetry)
    {h t₀ : ℝ} {k : ι → ℝ} (hh : 0 < h) (hk : ∀ i, 0 < k i) :
    Nonempty (AxisWallAtlasFamily A B h k t₀) :=
  ⟨fun i => Classical.choice (exists_axisWallArrivalAtlas A (B i) hh (hk i))⟩

end BianchiIX
