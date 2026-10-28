import BianchiIX.Measure.MainWallFirstTime

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal

namespace MainWallArrivalAtlas

variable {h k t₀ : ℝ} (C : MainWallArrivalAtlas h k t₀)

def firstPiece (B : Set SectionCoordinates) (I : Set ℝ) (n : ℕ) : Set SectionCoordinates :=
  {y | y ∈ (C.branch n).eligible B I ∧ (C.branch n).delay B I y = C.firstDelay B I y ∧
    ∀ m < n, (C.branch m).delay B I y ≠ C.firstDelay B I y}

theorem measurableSet_firstPiece {B : Set SectionCoordinates} {I : Set ℝ}
    (hB : MeasurableSet B) (hI : MeasurableSet I) (n : ℕ) : MeasurableSet (C.firstPiece B I n) := by
  have heq (m : ℕ) : MeasurableSet {y | (C.branch m).delay B I y = C.firstDelay B I y} :=
    measurableSet_eq_fun ((C.branch m).measurable_delay hB hI) (C.measurable_firstDelay hB hI)
  have hprev : MeasurableSet {y | ∀ m < n, (C.branch m).delay B I y ≠ C.firstDelay B I y} := by
    simp only [ofPred_forall]
    exact MeasurableSet.iInter (fun m => MeasurableSet.iInter (fun _ => (heq m).compl))
  exact ((C.branch n).measurableSet_eligible hB hI).inter ((heq n).inter hprev)

theorem firstPiece_pairwiseDisjoint (B : Set SectionCoordinates) (I : Set ℝ) :
    Pairwise (fun n m => Disjoint (C.firstPiece B I n) (C.firstPiece B I m)) := by
  intro n m hnm
  rw [disjoint_left]
  intro y hyn hym
  rcases lt_or_gt_of_ne hnm with hnm | hmn
  · exact hym.2.2 n hnm hyn.2.1
  · exact hyn.2.2 m hmn hym.2.1

theorem hittingDomain_eq_firstPieces {ε : ℝ} {B : Set SectionCoordinates} {I : Set ℝ}
    (hh : 0 < h) (hk : 0 < k) (hε : 0 < ε) (hI : I ⊆ Ici t₀)
    (hB : ∀ z ∈ B, mainWallChart k z 0 ≤ -ε) :
    mainWallHittingDomain h k t₀ B I = ⋃ n, C.firstPiece B I n := by
  classical
  ext y
  constructor
  · intro hy
    obtain ⟨m, _, hm, _⟩ := C.exists_firstDelay_branch hh hk hε hI hB hy
    have hex : ∃ n, (C.branch n).delay B I y = C.firstDelay B I y := ⟨m, hm⟩
    let n := Nat.find hex
    have hn : (C.branch n).delay B I y = C.firstDelay B I y := Nat.find_spec hex
    have heligible : y ∈ (C.branch n).eligible B I :=
      ((C.branch n).delay_lt_top_iff B I y).mp (hn ▸ (C.firstDelay_lt_top_iff B I y).mpr hy)
    exact mem_iUnion.mpr ⟨n, heligible, hn, fun _ hm => Nat.find_min hex hm⟩
  · intro hy
    obtain ⟨n, hn⟩ := mem_iUnion.mp hy
    apply (C.firstDelay_lt_top_iff B I y).mp
    rw [← hn.2.1]
    exact ((C.branch n).delay_lt_top_iff B I y).mpr hn.1

theorem firstPiece_isLeast {ε : ℝ} {B : Set SectionCoordinates} {I : Set ℝ}
    (hh : 0 < h) (hk : 0 < k) (hε : 0 < ε) (hI : I ⊆ Ici t₀)
    (hB : ∀ z ∈ B, mainWallChart k z 0 ≤ -ε) {n : ℕ} {y : SectionCoordinates}
    (hy : y ∈ C.firstPiece B I n) :
    IsLeast (mainWallHittingTimes h k t₀ B I y) ((C.branch n).coordinateTime y) := by
  have hdomain : y ∈ mainWallHittingDomain h k t₀ B I := by
    rw [C.hittingDomain_eq_firstPieces hh hk hε hI hB]
    exact mem_iUnion.mpr ⟨n, hy⟩
  obtain ⟨t, ht⟩ := exists_mainWall_first_time hh hk hε hI hB hdomain
  have H : ENNReal.ofReal ((C.branch n).coordinateTime y - t₀) = ENNReal.ofReal (t - t₀) :=
    ((C.branch n).delay_of_mem hy.1).symm.trans (hy.2.1.trans (C.firstDelay_of_isLeast ht).1)
  have heq := (ENNReal.ofReal_eq_ofReal_iff (sub_nonneg.mpr (hI hy.1.2.1))
    (sub_nonneg.mpr (hI ht.1.1))).mp H
  have htime : (C.branch n).coordinateTime y = t := sub_left_injective heq
  rwa [htime]

theorem exists_measurable_firstPiece_map {B : Set SectionCoordinates} {I : Set ℝ}
    (hB : MeasurableSet B) (hI : MeasurableSet I) :
    ∃ R : SectionCoordinates → SectionCoordinates, Measurable R ∧
      ∀ n, EqOn R (C.branch n).map (C.firstPiece B I n) := by
  classical
  let g (n : ℕ) : SectionCoordinates → SectionCoordinates :=
    (C.branch n).source.piecewise (C.branch n).map (fun _ => 0)
  have hg (n : ℕ) : Measurable (g n) :=
    (show ContinuousOn (C.branch n).map (C.branch n).source from
      fun y hy => ((C.branch n).map_regular y hy).continuousAt.continuousWithinAt).measurable_piecewise
        continuousOn_const (C.branch n).isOpen_source.measurableSet
  obtain ⟨R, hR, hpieces⟩ := exists_measurable_piecewise (C.firstPiece B I)
    (C.measurableSet_firstPiece hB hI) g hg (fun n m hnm y hy =>
      ((disjoint_left.mp (C.firstPiece_pairwiseDisjoint B I hnm)) hy.1 hy.2).elim)
  refine ⟨R, hR, fun n y hy => ?_⟩
  rw [hpieces n hy]
  exact piecewise_eq_of_mem _ _ _ hy.1.1

end MainWallArrivalAtlas

/-- The Borel first arrival is a countable Borel partition of actual smooth arrival branches. -/
theorem exists_mainWall_firstMap {h k t₀ ε : ℝ} {B : Set SectionCoordinates} {I : Set ℝ}
    (hh : 0 < h) (hk : 0 < k) (hε : 0 < ε) (hI : I ⊆ Ici t₀)
    (hbound : ∀ z ∈ B, mainWallChart k z 0 ≤ -ε)
    (hB : MeasurableSet B) (hImeas : MeasurableSet I) :
    ∃ (C : MainWallArrivalAtlas h k t₀) (R : SectionCoordinates → SectionCoordinates),
      Measurable R ∧ (∀ n, EqOn R (C.branch n).map (C.firstPiece B I n)) ∧
      mainWallHittingDomain h k t₀ B I = ⋃ n, C.firstPiece B I n ∧
      ∀ y ∈ mainWallHittingDomain h k t₀ B I, ∃ t,
        IsLeast (mainWallHittingTimes h k t₀ B I y) t ∧
        R y = mainWallCoordinates (normalizedMaxCurve (mainWallChart h y) t₀ t) := by
  obtain ⟨C⟩ := exists_mainWallArrivalAtlas (t₀ := t₀) hh hk
  obtain ⟨R, hR, hpieces⟩ := C.exists_measurable_firstPiece_map hB hImeas
  have hcover := C.hittingDomain_eq_firstPieces hh hk hε hI hbound
  refine ⟨C, R, hR, hpieces, hcover, fun y hy => ?_⟩
  obtain ⟨n, hn⟩ := mem_iUnion.mp (hcover ▸ hy)
  exact ⟨(C.branch n).coordinateTime y, C.firstPiece_isLeast hh hk hε hI hbound hn,
    (hpieces n hn).trans ((C.branch n).map_eq_coordinates hn.1.1)⟩

end BianchiIX
