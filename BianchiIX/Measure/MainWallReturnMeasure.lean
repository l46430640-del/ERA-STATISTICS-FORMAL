import BianchiIX.Measure.MainWallReturnInjectivity

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal

namespace MainWallArrivalAtlas

variable {h k t₀ : ℝ} (C : MainWallArrivalAtlas h k t₀)

theorem exists_measurable_firstPiece_jacobian {B : Set SectionCoordinates} {I : Set ℝ}
    (hh : 0 < h) (hk : 0 < k) (hB : MeasurableSet B) (hI : MeasurableSet I) :
    ∃ j : SectionCoordinates → ℝ≥0∞, Measurable j ∧
      ∀ n, EqOn j (fun y => ENNReal.ofReal ((C.branch n).jacobian y)) (C.firstPiece B I n) := by
  classical
  let g (n : ℕ) : SectionCoordinates → ℝ :=
    (C.branch n).source.piecewise (C.branch n).jacobian (fun _ => 0)
  have hg (n : ℕ) : Measurable (g n) :=
    ((C.branch n).continuousOn_jacobian hh hk).measurable_piecewise
      continuousOn_const (C.branch n).isOpen_source.measurableSet
  obtain ⟨j, hj, hpieces⟩ := exists_measurable_piecewise (C.firstPiece B I)
    (C.measurableSet_firstPiece hB hI) (fun n y => ENNReal.ofReal (g n y))
    (fun n => (hg n).ennreal_ofReal) (fun n m hnm y hy =>
      ((disjoint_left.mp (C.firstPiece_pairwiseDisjoint B I hnm)) hy.1 hy.2).elim)
  refine ⟨j, hj, fun n y hy => ?_⟩
  rw [hpieces n hy]
  change ENNReal.ofReal (g n y) = ENNReal.ofReal ((C.branch n).jacobian y)
  rw [show g n y = (C.branch n).jacobian y from piecewise_eq_of_mem _ _ _ hy.1.1]

/-- Injectivity makes the local image measures additive over the first-arrival partition. -/
theorem measure_image_of_firstPieces {B D A : Set SectionCoordinates} {I : Set ℝ}
    {R : SectionCoordinates → SectionCoordinates} {j : SectionCoordinates → ℝ≥0∞}
    (hh : 0 < h) (hB : MeasurableSet B) (hI : MeasurableSet I)
    (hcover : D ⊆ ⋃ n, C.firstPiece B I n) (hinj : InjOn R D)
    (hR : ∀ n, EqOn R (C.branch n).map (C.firstPiece B I n))
    (hj : ∀ n, EqOn j (fun y => ENNReal.ofReal ((C.branch n).jacobian y)) (C.firstPiece B I n))
    (hA : MeasurableSet A) (hAD : A ⊆ D) :
    MeasurableSet (R '' A) ∧ mainWallMeasure k (R '' A) = ∫⁻ y in A, j y ∂mainWallMeasure h := by
  let Q (n : ℕ) := A ∩ C.firstPiece B I n
  have hQ (n : ℕ) : MeasurableSet (Q n) := hA.inter (C.measurableSet_firstPiece hB hI n)
  have hQsource (n : ℕ) : Q n ⊆ (C.branch n).source := fun _ hy => hy.2.1.1
  have hQD (n : ℕ) : Q n ⊆ D := fun _ hy => hAD hy.1
  have hdisjoint : Pairwise (fun n m => Disjoint (Q n) (Q m)) :=
    fun _ _ hnm => (C.firstPiece_pairwiseDisjoint B I hnm).mono inter_subset_right inter_subset_right
  have hdecomp : A = ⋃ n, Q n := by
    ext y
    constructor
    · intro hy
      obtain ⟨n, hn⟩ := mem_iUnion.mp (hcover (hAD hy))
      exact mem_iUnion.mpr ⟨n, hy, hn⟩
    · intro hy
      obtain ⟨n, hn⟩ := mem_iUnion.mp hy
      exact hn.1
  have himage (n : ℕ) : R '' Q n = (C.branch n).map '' Q n :=
    ((hR n).mono inter_subset_right).image_eq
  have himageMeas (n : ℕ) : MeasurableSet (R '' Q n) := by
    rw [himage n]
    exact (C.branch n).measurableSet_image (hQ n) (hQsource n)
  have hRD : Pairwise (fun n m => Disjoint (R '' Q n) (R '' Q m)) := by
    intro n m hnm
    rw [disjoint_left]
    rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, heq⟩
    have hxy := hinj (hQD n hx) (hQD m hy) heq.symm
    exact disjoint_left.mp (hdisjoint hnm) hx (hxy ▸ hy)
  have hRdecomp : R '' A = ⋃ n, R '' Q n := by rw [hdecomp, image_iUnion]
  refine ⟨hRdecomp ▸ MeasurableSet.iUnion himageMeas, ?_⟩
  calc
    mainWallMeasure k (R '' A) = ∑' n, mainWallMeasure k (R '' Q n) := by
      rw [hRdecomp, measure_iUnion hRD himageMeas]
    _ = ∑' n, ∫⁻ y in Q n, j y ∂mainWallMeasure h := by
      apply tsum_congr
      intro n
      rw [himage n, (C.branch n).measure_image hh (hQ n) (hQsource n)]
      apply lintegral_congr_ae
      exact ae_restrict_of_forall_mem (hQ n) (fun y hy => (hj n hy.2).symm)
    _ = ∫⁻ y in A, j y ∂mainWallMeasure h := by
      rw [hdecomp, lintegral_iUnion hQ hdisjoint]

end MainWallArrivalAtlas

/-- The actual first return carries a Borel Jacobian and the global exact change-of-variables law. -/
theorem exists_mainWall_firstReturn {h t₀ ε : ℝ} {B : Set SectionCoordinates}
    (hh : 0 < h) (hε : 0 < ε) (hbound : ∀ z ∈ B, mainWallChart h z 0 ≤ -ε)
    (hB : MeasurableSet B) :
    ∃ (R : SectionCoordinates → SectionCoordinates) (j : SectionCoordinates → ℝ≥0∞),
      Measurable R ∧ Measurable j ∧ InjOn R (mainWallReturnDomain h t₀ B) ∧
      (∀ y ∈ mainWallReturnDomain h t₀ B, ∃ t,
        IsLeast (mainWallHittingTimes h h t₀ B (Ioi t₀) y) t ∧
        R y = mainWallCoordinates (normalizedMaxCurve (mainWallChart h y) t₀ t)) ∧
      (∀ y ∈ mainWallReturnDomain h t₀ B, 1 < j y ∧ j y < ∞) ∧
      (∀ A, MeasurableSet A → A ⊆ mainWallReturnDomain h t₀ B →
        MeasurableSet (R '' A) ∧ mainWallMeasure h (R '' A) = ∫⁻ y in A, j y ∂mainWallMeasure h) := by
  obtain ⟨C, R, hR, hpiecesR, hcover, hfirst⟩ := exists_mainWall_firstMap
    (t₀ := t₀) hh hh hε (show Ioi t₀ ⊆ Ici t₀ from fun x hx => show t₀ ≤ x from le_of_lt hx)
    hbound hB measurableSet_Ioi
  obtain ⟨j, hj, hpiecesJ⟩ := C.exists_measurable_firstPiece_jacobian hh hh hB measurableSet_Ioi
  have hfirstD : ∀ y ∈ mainWallReturnDomain h t₀ B, ∃ t,
      IsLeast (mainWallHittingTimes h h t₀ B (Ioi t₀) y) t ∧
      R y = mainWallCoordinates (normalizedMaxCurve (mainWallChart h y) t₀ t) := fun y hy => hfirst y hy.2
  have hinj := mainWall_firstReturn_injOn hh hfirstD
  have hcoverD : mainWallReturnDomain h t₀ B ⊆ ⋃ n, C.firstPiece B (Ioi t₀) n :=
    fun _ hy => hcover ▸ hy.2
  refine ⟨R, j, hR, hj, hinj, hfirstD, ?_, ?_⟩
  · intro y hy
    obtain ⟨n, hn⟩ := mem_iUnion.mp (hcoverD hy)
    rw [hpiecesJ n hn]
    exact ⟨ENNReal.one_lt_ofReal.mpr ((C.branch n).jacobian_gt_one hh hh hn.1.1 hn.1.2.1),
      ENNReal.ofReal_lt_top⟩
  · intro A hA hAD
    exact C.measure_image_of_firstPieces hh hB measurableSet_Ioi hcoverD hinj hpiecesR hpiecesJ hA hAD

end BianchiIX
