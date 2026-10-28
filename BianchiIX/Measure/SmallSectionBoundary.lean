import BianchiIX.Measure.RadialPartitionNull
import BianchiIX.Measure.MainWallRegionStatistics

noncomputable section

namespace BianchiIX

open Set MeasureTheory

def mainWallSectionBoundary (d : ℝ) : Set SectionCoordinates :=
  mainWallSmallSection d \ mainWallOpenSection d

def mainWallClosedFailure (d : ℝ) (E : Set SectionCoordinates) : Set SectionCoordinates :=
  mainWallSectionBoundary d ∪ E

theorem mainWallOpenSection_subset_small (d : ℝ) : mainWallOpenSection d ⊆ mainWallSmallSection d :=
  fun _ hz => ⟨hz.1.le, hz.2.le⟩

theorem measurableSet_mainWallSectionBoundary (d : ℝ) : MeasurableSet (mainWallSectionBoundary d) :=
  (measurableSet_mainWallSmallSection d).diff (measurableSet_mainWallOpenSection d)

theorem volume_mainWallSectionBoundary (d : ℝ) : volume (mainWallSectionBoundary d) = 0 := by
  have H : volume (({z : SectionCoordinates | z 0 = d} ∪ {z | z 0 = -d}) ∪
      ({z | Real.exp (-z 1) = d} ∪ {z | Real.exp (-z 2) = d})) = 0 :=
    measure_union_null (measure_union_null (volume_sectionCoordinate_level 0 d)
      (volume_sectionCoordinate_level 0 (-d)))
      (measure_union_null (volume_sectionWall_level 1 d) (volume_sectionWall_level 2 d))
  apply measure_mono_null _ H
  intro z hz
  by_cases hs : |z 0| < d
  · have hm : max (Real.exp (-z 1)) (Real.exp (-z 2)) = d :=
      le_antisymm hz.1.2 (le_of_not_gt (fun hm => hz.2 ⟨hs, hm⟩))
    apply Or.inr
    rcases le_total (Real.exp (-z 1)) (Real.exp (-z 2)) with hw | hw
    · exact Or.inr (by simpa only [mem_ofPred_eq, max_eq_right hw] using hm)
    · exact Or.inl (by simpa only [mem_ofPred_eq, max_eq_left hw] using hm)
  · have heq : |z 0| = d := le_antisymm hz.1.1 (le_of_not_gt hs)
    apply Or.inl
    rcases le_total 0 (z 0) with ht | ht
    · exact Or.inl (by simpa only [mem_ofPred_eq, abs_of_nonneg ht] using heq)
    · exact Or.inr (by rw [abs_of_nonpos ht] at heq; change z 0 = -d; linarith)

theorem mainWallOriginalMeasure_sectionBoundary (h d : ℝ) :
    mainWallOriginalMeasure h (mainWallSectionBoundary d) = 0 := by
  apply withDensity_absolutelyContinuous _ _
  exact Measure.absolutelyContinuous_restrict (volume_mainWallSectionBoundary d)

theorem mainWallMeasure_sectionBoundary (h d : ℝ) :
    mainWallMeasure h (mainWallSectionBoundary d) = 0 := by
  apply withDensity_absolutelyContinuous _ _
  exact Measure.absolutelyContinuous_restrict (volume_mainWallSectionBoundary d)

theorem measurableSet_mainWallClosedFailure (d : ℝ) {E : Set SectionCoordinates}
    (hE : MeasurableSet E) : MeasurableSet (mainWallClosedFailure d E) :=
  (measurableSet_mainWallSectionBoundary d).union hE

theorem mainWallClosedFailure_subset {d : ℝ} {E : Set SectionCoordinates}
    (hE : E ⊆ mainWallOpenSection d) : mainWallClosedFailure d E ⊆ mainWallSmallSection d := by
  rintro z (hb | he)
  · exact hb.1
  · exact mainWallOpenSection_subset_small d (hE he)

/-- Adding only the outer boundary preserves the successful target exactly. -/
theorem mainWallClosedFailure_complement (d : ℝ) (E : Set SectionCoordinates) :
    mainWallSmallSection d \ mainWallClosedFailure d E = mainWallOpenSection d \ E := by
  ext z
  constructor
  · rintro ⟨hz, hn⟩
    exact ⟨by by_contra ho; exact hn (Or.inl ⟨hz, ho⟩), fun he => hn (Or.inr he)⟩
  · rintro ⟨hz, hn⟩
    exact ⟨mainWallOpenSection_subset_small d hz, fun he => he.elim (fun hb => hb.2 hz) hn⟩

theorem mainWallOriginalMeasure_closedFailure (h d : ℝ) (E : Set SectionCoordinates) :
    mainWallOriginalMeasure h (mainWallClosedFailure d E) = mainWallOriginalMeasure h E := by
  apply le_antisymm _ (measure_mono subset_union_right)
  exact (measure_union_le _ _).trans_eq (by rw [mainWallOriginalMeasure_sectionBoundary, zero_add])

theorem mainWallMeasure_closedFailure (h d : ℝ) (E : Set SectionCoordinates) :
    mainWallMeasure h (mainWallClosedFailure d E) = mainWallMeasure h E := by
  apply le_antisymm _ (measure_mono subset_union_right)
  exact (measure_union_le _ _).trans_eq (by rw [mainWallMeasure_sectionBoundary, zero_add])

end BianchiIX
