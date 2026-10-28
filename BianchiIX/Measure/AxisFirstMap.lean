import BianchiIX.Measure.AxisFirstTime

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal

namespace AxisWallAtlasFamily

variable {ι : Type*} [Encodable ι] {A : NormalizedSymmetry} {B : ι → NormalizedSymmetry}
  {h t₀ : ℝ} {k : ι → ℝ} (C : AxisWallAtlasFamily A B h k t₀)

/-- Choose the first encoded target and branch among those attaining the true earliest time. -/
def firstPiece (E : ι → Set SectionCoordinates) (I : Set ℝ) (q : ι × ℕ) : Set SectionCoordinates :=
  {y | y ∈ ((C q.1).branch q.2).eligible (E q.1) I ∧
    ((C q.1).branch q.2).delay (E q.1) I y = C.firstDelay E I y ∧
    ∀ r : ι × ℕ, Encodable.encode r < Encodable.encode q →
      ((C r.1).branch r.2).delay (E r.1) I y ≠ C.firstDelay E I y}

theorem measurableSet_firstPiece {E : ι → Set SectionCoordinates} {I : Set ℝ}
    (hE : ∀ i, MeasurableSet (E i)) (hI : MeasurableSet I) (q : ι × ℕ) :
    MeasurableSet (C.firstPiece E I q) := by
  have heq (r : ι × ℕ) : MeasurableSet {y |
      ((C r.1).branch r.2).delay (E r.1) I y = C.firstDelay E I y} :=
    measurableSet_eq_fun (((C r.1).branch r.2).measurable_delay (hE r.1) hI) (C.measurable_firstDelay hE hI)
  have hprev : MeasurableSet {y | ∀ r : ι × ℕ, Encodable.encode r < Encodable.encode q →
      ((C r.1).branch r.2).delay (E r.1) I y ≠ C.firstDelay E I y} := by
    simp only [ofPred_forall]
    exact MeasurableSet.iInter (fun r => MeasurableSet.iInter (fun _ => (heq r).compl))
  exact (((C q.1).branch q.2).measurableSet_eligible (hE q.1) hI).inter ((heq q).inter hprev)

theorem firstPiece_pairwiseDisjoint (E : ι → Set SectionCoordinates) (I : Set ℝ) :
    Pairwise (fun q r => Disjoint (C.firstPiece E I q) (C.firstPiece E I r)) := by
  intro q r hqr
  rw [disjoint_left]
  intro y hyq hyr
  have hcode : Encodable.encode q ≠ Encodable.encode r := fun heq => hqr (Encodable.encode_injective heq)
  rcases lt_or_gt_of_ne hcode with hlt | hgt
  · exact hyr.2.2 q hlt hyq.2.1
  · exact hyq.2.2 r hgt hyr.2.1

theorem hittingDomain_eq_firstPieces [Finite ι] {ε : ι → ℝ}
    {E : ι → Set SectionCoordinates} {I : Set ℝ}
    (hh : 0 < h) (hk : ∀ i, 0 < k i) (hε : ∀ i, 0 < ε i) (hI : I ⊆ Ici t₀)
    (hbound : ∀ i, ∀ z ∈ E i, mainWallChart (k i) z 0 ≤ -ε i) :
    axisFamilyHittingDomain A B h k t₀ E I = ⋃ q, C.firstPiece E I q := by
  classical
  ext y
  constructor
  · intro hy
    obtain ⟨i, n, _, hn, _⟩ := C.exists_firstDelay_branch hh hk hε hI hbound hy
    have hex : ∃ m : ℕ, ∃ q : ι × ℕ, Encodable.encode q = m ∧
        ((C q.1).branch q.2).delay (E q.1) I y = C.firstDelay E I y :=
      ⟨Encodable.encode (i, n), (i, n), rfl, hn⟩
    obtain ⟨q, hq, heq⟩ := Nat.find_spec hex
    have heligible : y ∈ ((C q.1).branch q.2).eligible (E q.1) I :=
      (((C q.1).branch q.2).delay_lt_top_iff (E q.1) I y).mp
        (heq ▸ (C.firstDelay_lt_top_iff E I y).mpr hy)
    refine mem_iUnion.mpr ⟨q, heligible, heq, fun r hr he => ?_⟩
    exact Nat.find_min hex (hq ▸ hr) ⟨r, rfl, he⟩
  · intro hy
    obtain ⟨q, hq⟩ := mem_iUnion.mp hy
    apply (C.firstDelay_lt_top_iff E I y).mp
    rw [← hq.2.1]
    exact (((C q.1).branch q.2).delay_lt_top_iff (E q.1) I y).mpr hq.1

theorem firstPiece_isLeast [Finite ι] {ε : ι → ℝ}
    {E : ι → Set SectionCoordinates} {I : Set ℝ}
    (hh : 0 < h) (hk : ∀ i, 0 < k i) (hε : ∀ i, 0 < ε i) (hI : I ⊆ Ici t₀)
    (hbound : ∀ i, ∀ z ∈ E i, mainWallChart (k i) z 0 ≤ -ε i)
    {q : ι × ℕ} {y : SectionCoordinates} (hy : y ∈ C.firstPiece E I q) :
    IsLeast (axisFamilyHittingTimes A B h k t₀ E I y) (((C q.1).branch q.2).coordinateTime y) := by
  have hdomain : y ∈ axisFamilyHittingDomain A B h k t₀ E I := by
    rw [C.hittingDomain_eq_firstPieces hh hk hε hI hbound]
    exact mem_iUnion.mpr ⟨q, hy⟩
  obtain ⟨t, ht⟩ := exists_axisFamily_first_time A B hh hk hε hI hbound hdomain
  have H : ENNReal.ofReal (((C q.1).branch q.2).coordinateTime y - t₀) = ENNReal.ofReal (t - t₀) :=
    (((C q.1).branch q.2).delay_of_mem hy.1).symm.trans (hy.2.1.trans (C.firstDelay_of_isLeast ht).1)
  have heq := (ENNReal.ofReal_eq_ofReal_iff (sub_nonneg.mpr (hI hy.1.2.1))
    (sub_nonneg.mpr (hI ht.1.1))).mp H
  have htime : ((C q.1).branch q.2).coordinateTime y = t := sub_left_injective heq
  rwa [htime]

theorem exists_measurable_firstPiece_map [Nonempty ι] [MeasurableSpace ι]
    {E : ι → Set SectionCoordinates} {I : Set ℝ}
    (hE : ∀ i, MeasurableSet (E i)) (hI : MeasurableSet I) :
    ∃ R : SectionCoordinates → ι × SectionCoordinates, Measurable R ∧
      ∀ q : ι × ℕ, EqOn R (fun y => (q.1, ((C q.1).branch q.2).map y)) (C.firstPiece E I q) := by
  classical
  let g (q : ι × ℕ) : SectionCoordinates → ι × SectionCoordinates := fun y =>
    (q.1, ((C q.1).branch q.2).source.piecewise ((C q.1).branch q.2).map (fun _ => 0) y)
  have hg (q : ι × ℕ) : Measurable (g q) := by
    have hm : Measurable (((C q.1).branch q.2).source.piecewise
        ((C q.1).branch q.2).map (fun _ => 0)) :=
      (show ContinuousOn ((C q.1).branch q.2).map ((C q.1).branch q.2).source from
      fun y hy => (((C q.1).branch q.2).map_regular y hy).continuousAt.continuousWithinAt).measurable_piecewise
        continuousOn_const ((C q.1).branch q.2).isOpen_source.measurableSet
    exact measurable_const.prodMk hm
  obtain ⟨R, hR, hpieces⟩ := exists_measurable_piecewise (C.firstPiece E I)
    (C.measurableSet_firstPiece hE hI) g hg (fun q r hqr y hy =>
      ((disjoint_left.mp (C.firstPiece_pairwiseDisjoint E I hqr)) hy.1 hy.2).elim)
  refine ⟨R, hR, fun q y hy => ?_⟩
  rw [hpieces q hy]
  exact congrArg (fun z => (q.1, z)) (piecewise_eq_of_mem _ _ _ hy.1.1)

end AxisWallAtlasFamily

/-- A Borel first arrival in a finite target family, with a target label chosen on disjoint source pieces. -/
theorem exists_axisFamily_firstMap {ι : Type*} [Finite ι] [Encodable ι] [Nonempty ι] [MeasurableSpace ι]
    (A : NormalizedSymmetry) (B : ι → NormalizedSymmetry) {h t₀ : ℝ} {k ε : ι → ℝ}
    {E : ι → Set SectionCoordinates} {I : Set ℝ}
    (hh : 0 < h) (hk : ∀ i, 0 < k i) (hε : ∀ i, 0 < ε i) (hI : I ⊆ Ici t₀)
    (hbound : ∀ i, ∀ z ∈ E i, mainWallChart (k i) z 0 ≤ -ε i)
    (hE : ∀ i, MeasurableSet (E i)) (hImeas : MeasurableSet I) :
    ∃ (C : AxisWallAtlasFamily A B h k t₀) (R : SectionCoordinates → ι × SectionCoordinates),
      Measurable R ∧
      (∀ q : ι × ℕ, EqOn R (fun y => (q.1, ((C q.1).branch q.2).map y)) (C.firstPiece E I q)) ∧
      axisFamilyHittingDomain A B h k t₀ E I = ⋃ q, C.firstPiece E I q ∧
      ∀ y ∈ axisFamilyHittingDomain A B h k t₀ E I, ∃ t,
        IsLeast (axisFamilyHittingTimes A B h k t₀ E I y) t ∧
        (y, t) ∈ axisWallArrivalRelation A (B (R y).1) h (k (R y).1) t₀ ∧
        (R y).2 = axisWallCoordinates (B (R y).1) (normalizedMaxCurve (axisWallChart A h y) t₀ t) ∧
        (R y).2 ∈ E (R y).1 := by
  obtain ⟨C⟩ := exists_axisWallAtlasFamily A B (t₀ := t₀) hh hk
  obtain ⟨R, hR, hpieces⟩ := C.exists_measurable_firstPiece_map hE hImeas
  have hcover := C.hittingDomain_eq_firstPieces hh hk hε hI hbound
  refine ⟨C, R, hR, hpieces, hcover, fun y hy => ?_⟩
  obtain ⟨q, hq⟩ := mem_iUnion.mp (hcover ▸ hy)
  refine ⟨((C q.1).branch q.2).coordinateTime y, C.firstPiece_isLeast hh hk hε hI hbound hq, ?_⟩
  rw [hpieces q hq]
  exact ⟨((C q.1).branch q.2).mem_relation hq.1.1,
    ((C q.1).branch q.2).map_eq_coordinates hq.1.1, hq.1.2.2⟩

end BianchiIX
