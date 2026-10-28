import BianchiIX.Dynamics.AxisAtlas
import BianchiIX.Measure.AxisArrivalMeasure

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal

namespace AxisWallArrival

variable {A B : NormalizedSymmetry} {h k t₀ : ℝ} (P : AxisWallArrival A B h k t₀)

def eligible (E : Set SectionCoordinates) (I : Set ℝ) : Set SectionCoordinates :=
  {y | y ∈ P.source ∧ P.coordinateTime y ∈ I ∧ P.map y ∈ E}

theorem measurableSet_eligible {E : Set SectionCoordinates} {I : Set ℝ}
    (hE : MeasurableSet E) (hI : MeasurableSet I) : MeasurableSet (P.eligible E I) := by
  have ht := P.continuousOn_coordinateTime.domRestrict.measurable
  have hm := (show ContinuousOn P.map P.source from
    fun y hy => (P.map_regular y hy).continuousAt.continuousWithinAt).domRestrict.measurable
  have H := P.isOpen_source.measurableSet.subtype_image ((hI.preimage ht).inter (hE.preimage hm))
  convert! H using 1
  ext y
  simp only [eligible, mem_ofPred_eq, mem_image, mem_inter_iff, mem_preimage, domRestrict_apply]
  aesop

def delay (E : Set SectionCoordinates) (I : Set ℝ) : SectionCoordinates → ℝ≥0∞ := by
  classical
  exact (P.eligible E I).piecewise (fun y => ENNReal.ofReal (P.coordinateTime y - t₀)) (fun _ => ∞)

theorem delay_of_mem {E : Set SectionCoordinates} {I : Set ℝ} {y : SectionCoordinates}
    (hy : y ∈ P.eligible E I) : P.delay E I y = ENNReal.ofReal (P.coordinateTime y - t₀) := by
  classical
  simp only [delay, piecewise_eq_of_mem _ _ _ hy]

theorem delay_lt_top_iff (E : Set SectionCoordinates) (I : Set ℝ) (y : SectionCoordinates) :
    P.delay E I y < ∞ ↔ y ∈ P.eligible E I := by
  classical
  by_cases hy : y ∈ P.eligible E I <;> simp [delay, hy]

theorem measurable_delay {E : Set SectionCoordinates} {I : Set ℝ}
    (hE : MeasurableSet E) (hI : MeasurableSet I) : Measurable (P.delay E I) := by
  classical
  have hc : ContinuousOn (fun y => ENNReal.ofReal (P.coordinateTime y - t₀)) (P.eligible E I) :=
    ENNReal.continuous_ofReal.comp_continuousOn
      ((P.continuousOn_coordinateTime.mono (fun _ hy => hy.1)).sub continuousOn_const)
  exact hc.measurable_piecewise continuousOn_const (P.measurableSet_eligible hE hI)

end AxisWallArrival

/-- Actual target hits; labels may overlap and are not identified with disjoint physical sections. -/
def axisFamilyHittingTimes {ι : Type*} (A : NormalizedSymmetry) (B : ι → NormalizedSymmetry)
    (h : ℝ) (k : ι → ℝ) (t₀ : ℝ) (E : ι → Set SectionCoordinates) (I : Set ℝ)
    (y : SectionCoordinates) : Set ℝ :=
  {t | t ∈ I ∧ ∃ i, (y, t) ∈ axisWallArrivalRelation A (B i) h (k i) t₀ ∧
    axisWallCoordinates (B i) (normalizedMaxCurve (axisWallChart A h y) t₀ t) ∈ E i}

def axisFamilyHittingDomain {ι : Type*} (A : NormalizedSymmetry) (B : ι → NormalizedSymmetry)
    (h : ℝ) (k : ι → ℝ) (t₀ : ℝ) (E : ι → Set SectionCoordinates) (I : Set ℝ) : Set SectionCoordinates :=
  {y | (axisFamilyHittingTimes A B h k t₀ E I y).Nonempty}

namespace AxisWallAtlasFamily

variable {ι : Type*} {A : NormalizedSymmetry} {B : ι → NormalizedSymmetry}
  {h t₀ : ℝ} {k : ι → ℝ} (C : AxisWallAtlasFamily A B h k t₀)

theorem hittingDomain_eq_iUnion (E : ι → Set SectionCoordinates) (I : Set ℝ) :
    axisFamilyHittingDomain A B h k t₀ E I = ⋃ i, ⋃ n, ((C i).branch n).eligible (E i) I := by
  ext y
  constructor
  · rintro ⟨t, ht, i, hrel, hE⟩
    obtain ⟨n, hy, htime⟩ := ((C i).mem_relation_iff y t).mp hrel
    refine mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨n, hy, ?_, ?_⟩⟩
    · rwa [htime]
    · rwa [((C i).branch n).map_eq_coordinates hy, htime]
  · intro hy
    obtain ⟨i, hi⟩ := mem_iUnion.mp hy
    obtain ⟨n, hn⟩ := mem_iUnion.mp hi
    refine ⟨((C i).branch n).coordinateTime y, hn.2.1, i, ((C i).branch n).mem_relation hn.1, ?_⟩
    rw [← ((C i).branch n).map_eq_coordinates hn.1]
    exact hn.2.2

include C in
theorem measurableSet_hittingDomain [Countable ι] {E : ι → Set SectionCoordinates} {I : Set ℝ}
    (hE : ∀ i, MeasurableSet (E i)) (hI : MeasurableSet I) :
    MeasurableSet (axisFamilyHittingDomain A B h k t₀ E I) := by
  rw [C.hittingDomain_eq_iUnion E I]
  exact MeasurableSet.iUnion (fun i => MeasurableSet.iUnion
    (fun n => ((C i).branch n).measurableSet_eligible (hE i) hI))

def firstDelay (E : ι → Set SectionCoordinates) (I : Set ℝ) (y : SectionCoordinates) : ℝ≥0∞ :=
  ⨅ i, ⨅ n, ((C i).branch n).delay (E i) I y

theorem measurable_firstDelay [Countable ι] {E : ι → Set SectionCoordinates} {I : Set ℝ}
    (hE : ∀ i, MeasurableSet (E i)) (hI : MeasurableSet I) : Measurable (C.firstDelay E I) :=
  Measurable.iInf (fun i => Measurable.iInf (fun n => ((C i).branch n).measurable_delay (hE i) hI))

theorem firstDelay_lt_top_iff (E : ι → Set SectionCoordinates) (I : Set ℝ) (y : SectionCoordinates) :
    C.firstDelay E I y < ∞ ↔ y ∈ axisFamilyHittingDomain A B h k t₀ E I := by
  rw [C.hittingDomain_eq_iUnion E I]
  simp only [firstDelay, iInf_lt_iff, AxisWallArrival.delay_lt_top_iff, mem_iUnion]

end AxisWallAtlasFamily

theorem measurableSet_axisFamilyHittingDomain {ι : Type*} [Countable ι]
    (A : NormalizedSymmetry) (B : ι → NormalizedSymmetry) {h t₀ : ℝ} {k : ι → ℝ}
    (hh : 0 < h) (hk : ∀ i, 0 < k i) {E : ι → Set SectionCoordinates} {I : Set ℝ}
    (hE : ∀ i, MeasurableSet (E i)) (hI : MeasurableSet I) :
    MeasurableSet (axisFamilyHittingDomain A B h k t₀ E I) := by
  obtain ⟨C⟩ := exists_axisWallAtlasFamily A B (t₀ := t₀) hh hk
  exact C.measurableSet_hittingDomain hE hI

end BianchiIX
