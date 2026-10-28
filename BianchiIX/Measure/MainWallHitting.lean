import BianchiIX.Dynamics.MainWallAtlas
import BianchiIX.Measure.MainWallMeasure

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal

namespace MainWallArrival

variable {h k t₀ : ℝ} (P : MainWallArrival h k t₀)

def eligible (B : Set SectionCoordinates) (I : Set ℝ) : Set SectionCoordinates :=
  {y | y ∈ P.source ∧ P.coordinateTime y ∈ I ∧ P.map y ∈ B}

theorem measurableSet_eligible {B : Set SectionCoordinates} {I : Set ℝ}
    (hB : MeasurableSet B) (hI : MeasurableSet I) : MeasurableSet (P.eligible B I) := by
  have ht := P.continuousOn_coordinateTime.domRestrict.measurable
  have hm := (show ContinuousOn P.map P.source from
    fun y hy => (P.map_regular y hy).continuousAt.continuousWithinAt).domRestrict.measurable
  have H := P.isOpen_source.measurableSet.subtype_image ((hI.preimage ht).inter (hB.preimage hm))
  convert! H using 1
  ext y
  simp only [eligible, mem_ofPred_eq, mem_image, mem_inter_iff, mem_preimage, domRestrict_apply]
  aesop

/-- The nonnegative elapsed time, with infinity when this branch is ineligible. -/
def delay (B : Set SectionCoordinates) (I : Set ℝ) : SectionCoordinates → ℝ≥0∞ := by
  classical
  exact (P.eligible B I).piecewise (fun y => ENNReal.ofReal (P.coordinateTime y - t₀)) (fun _ => ∞)

theorem delay_of_mem {B : Set SectionCoordinates} {I : Set ℝ} {y : SectionCoordinates}
    (hy : y ∈ P.eligible B I) : P.delay B I y = ENNReal.ofReal (P.coordinateTime y - t₀) := by
  classical
  simp only [delay, piecewise_eq_of_mem _ _ _ hy]

theorem delay_lt_top_iff (B : Set SectionCoordinates) (I : Set ℝ) (y : SectionCoordinates) :
    P.delay B I y < ∞ ↔ y ∈ P.eligible B I := by
  classical
  by_cases hy : y ∈ P.eligible B I <;> simp [delay, hy]

theorem measurable_delay {B : Set SectionCoordinates} {I : Set ℝ}
    (hB : MeasurableSet B) (hI : MeasurableSet I) : Measurable (P.delay B I) := by
  classical
  have hc : ContinuousOn (fun y => ENNReal.ofReal (P.coordinateTime y - t₀)) (P.eligible B I) :=
    ENNReal.continuous_ofReal.comp_continuousOn
      ((P.continuousOn_coordinateTime.mono (fun _ hy => hy.1)).sub continuousOn_const)
  exact hc.measurable_piecewise continuousOn_const (P.measurableSet_eligible hB hI)

end MainWallArrival

def mainWallHittingDomain (h k t₀ : ℝ) (B : Set SectionCoordinates) (I : Set ℝ) : Set SectionCoordinates :=
  {y | ∃ t ∈ I, (y, t) ∈ mainWallArrivalRelation h k t₀ ∧
    mainWallCoordinates (normalizedMaxCurve (mainWallChart h y) t₀ t) ∈ B}

namespace MainWallArrivalAtlas

variable {h k t₀ : ℝ} (C : MainWallArrivalAtlas h k t₀)

theorem hittingDomain_eq_iUnion (B : Set SectionCoordinates) (I : Set ℝ) :
    mainWallHittingDomain h k t₀ B I = ⋃ n, (C.branch n).eligible B I := by
  ext y
  constructor
  · rintro ⟨t, ht, hrel, hB⟩
    obtain ⟨n, hy, htime⟩ := (C.mem_relation_iff y t).mp hrel
    refine mem_iUnion.mpr ⟨n, hy, ?_, ?_⟩
    · rwa [htime]
    · rwa [(C.branch n).map_eq_coordinates hy, htime]
  · intro hy
    obtain ⟨n, hn⟩ := mem_iUnion.mp hy
    refine ⟨(C.branch n).coordinateTime y, hn.2.1, (C.branch n).mem_relation hn.1, ?_⟩
    rw [← (C.branch n).map_eq_coordinates hn.1]
    exact hn.2.2

include C in
theorem measurableSet_hittingDomain {B : Set SectionCoordinates} {I : Set ℝ}
    (hB : MeasurableSet B) (hI : MeasurableSet I) : MeasurableSet (mainWallHittingDomain h k t₀ B I) := by
  rw [C.hittingDomain_eq_iUnion B I]
  exact MeasurableSet.iUnion (fun n => (C.branch n).measurableSet_eligible hB hI)

def firstDelay (B : Set SectionCoordinates) (I : Set ℝ) (y : SectionCoordinates) : ℝ≥0∞ :=
  ⨅ n, (C.branch n).delay B I y

theorem measurable_firstDelay {B : Set SectionCoordinates} {I : Set ℝ}
    (hB : MeasurableSet B) (hI : MeasurableSet I) : Measurable (C.firstDelay B I) :=
  Measurable.iInf (fun n => (C.branch n).measurable_delay hB hI)

theorem firstDelay_lt_top_iff (B : Set SectionCoordinates) (I : Set ℝ) (y : SectionCoordinates) :
    C.firstDelay B I y < ∞ ↔ y ∈ mainWallHittingDomain h k t₀ B I := by
  rw [C.hittingDomain_eq_iUnion B I]
  simp only [firstDelay, iInf_lt_iff, MainWallArrival.delay_lt_top_iff, mem_iUnion]

end MainWallArrivalAtlas

theorem measurableSet_mainWallHittingDomain {h k t₀ : ℝ} (hh : 0 < h) (hk : 0 < k)
    {B : Set SectionCoordinates} {I : Set ℝ} (hB : MeasurableSet B) (hI : MeasurableSet I) :
    MeasurableSet (mainWallHittingDomain h k t₀ B I) := by
  obtain ⟨C⟩ := exists_mainWallArrivalAtlas (t₀ := t₀) hh hk
  exact C.measurableSet_hittingDomain hB hI

end BianchiIX
