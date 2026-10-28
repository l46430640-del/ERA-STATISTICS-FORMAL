import BianchiIX.Measure.AxisReturnMap
import BianchiIX.Measure.AxisFamilyMeasure

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal

namespace AxisWallAtlasFamily

variable {ι : Type*} [Encodable ι] [Nonempty ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  {A : NormalizedSymmetry} {B : ι → NormalizedSymmetry} {h t₀ : ℝ} {k : ι → ℝ}
  (C : AxisWallAtlasFamily A B h k t₀)

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
theorem exists_measurable_firstPiece_jacobian {E : ι → Set SectionCoordinates} {I : Set ℝ}
    (hh : 0 < h) (hk : ∀ i, 0 < k i) (hE : ∀ i, MeasurableSet (E i)) (hI : MeasurableSet I) :
    ∃ j : SectionCoordinates → ℝ≥0∞, Measurable j ∧
      ∀ q : ι × ℕ, EqOn j (fun y => ENNReal.ofReal (((C q.1).branch q.2).jacobian y)) (C.firstPiece E I q) := by
  classical
  let g (q : ι × ℕ) : SectionCoordinates → ℝ :=
    ((C q.1).branch q.2).source.piecewise ((C q.1).branch q.2).jacobian (fun _ => 0)
  have hg (q : ι × ℕ) : Measurable (g q) :=
    (((C q.1).branch q.2).continuousOn_jacobian hh (hk q.1)).measurable_piecewise
      continuousOn_const ((C q.1).branch q.2).isOpen_source.measurableSet
  obtain ⟨j, hj, hpieces⟩ := exists_measurable_piecewise (C.firstPiece E I)
    (C.measurableSet_firstPiece hE hI) (fun q y => ENNReal.ofReal (g q y))
    (fun q => (hg q).ennreal_ofReal) (fun q r hqr y hy =>
      ((disjoint_left.mp (C.firstPiece_pairwiseDisjoint E I hqr)) hy.1 hy.2).elim)
  refine ⟨j, hj, fun q y hy => ?_⟩
  rw [hpieces q hy]
  change ENNReal.ofReal (g q y) = ENNReal.ofReal (((C q.1).branch q.2).jacobian y)
  rw [show g q y = ((C q.1).branch q.2).jacobian y from piecewise_eq_of_mem _ _ _ hy.1.1]

omit [Nonempty ι] in
theorem measure_image_of_firstPieces {E : ι → Set SectionCoordinates} {D S : Set SectionCoordinates}
    {I : Set ℝ} {R : SectionCoordinates → ι × SectionCoordinates} {j : SectionCoordinates → ℝ≥0∞}
    (hh : 0 < h) (hE : ∀ i, MeasurableSet (E i)) (hI : MeasurableSet I)
    (hcover : D ⊆ ⋃ q, C.firstPiece E I q) (hinj : InjOn R D)
    (hR : ∀ q : ι × ℕ, EqOn R (fun y => (q.1, ((C q.1).branch q.2).map y)) (C.firstPiece E I q))
    (hj : ∀ q : ι × ℕ, EqOn j (fun y => ENNReal.ofReal (((C q.1).branch q.2).jacobian y)) (C.firstPiece E I q))
    (hS : MeasurableSet S) (hSD : S ⊆ D) :
    MeasurableSet (R '' S) ∧ axisFamilyMeasure k (R '' S) = ∫⁻ y in S, j y ∂mainWallMeasure h := by
  let Q (q : ι × ℕ) := S ∩ C.firstPiece E I q
  have hQ (q : ι × ℕ) : MeasurableSet (Q q) := hS.inter (C.measurableSet_firstPiece hE hI q)
  have hQsource (q : ι × ℕ) : Q q ⊆ ((C q.1).branch q.2).source := fun _ hy => hy.2.1.1
  have hQD (q : ι × ℕ) : Q q ⊆ D := fun _ hy => hSD hy.1
  have hdisjoint : Pairwise (fun q r => Disjoint (Q q) (Q r)) :=
    fun _ _ hqr => (C.firstPiece_pairwiseDisjoint E I hqr).mono inter_subset_right inter_subset_right
  have hdecomp : S = ⋃ q, Q q := by
    ext y
    constructor
    · intro hy
      obtain ⟨q, hq⟩ := mem_iUnion.mp (hcover (hSD hy))
      exact mem_iUnion.mpr ⟨q, hy, hq⟩
    · intro hy
      obtain ⟨q, hq⟩ := mem_iUnion.mp hy
      exact hq.1
  have himage (q : ι × ℕ) : R '' Q q = Prod.mk q.1 '' (((C q.1).branch q.2).map '' Q q) := by
    rw [← image_comp]
    exact ((hR q).mono inter_subset_right).image_eq
  have himageMeas (q : ι × ℕ) : MeasurableSet (R '' Q q) := by
    rw [himage q]
    exact (measurableEmbedding_prodMk_left q.1).measurableSet_image.mpr
      (((C q.1).branch q.2).measurableSet_image (hQ q) (hQsource q))
  have hRD : Pairwise (fun q r => Disjoint (R '' Q q) (R '' Q r)) := by
    intro q r hqr
    rw [disjoint_left]
    rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, heq⟩
    have hxy := hinj (hQD q hx) (hQD r hy) heq.symm
    exact disjoint_left.mp (hdisjoint hqr) hx (hxy ▸ hy)
  have hRdecomp : R '' S = ⋃ q, R '' Q q := by rw [hdecomp, image_iUnion]
  refine ⟨hRdecomp ▸ MeasurableSet.iUnion himageMeas, ?_⟩
  calc
    axisFamilyMeasure k (R '' S) = ∑' q, axisFamilyMeasure k (R '' Q q) := by
      rw [hRdecomp, measure_iUnion hRD himageMeas]
    _ = ∑' q, ∫⁻ y in Q q, j y ∂mainWallMeasure h := by
      apply tsum_congr
      intro q
      rw [himage q, axisFamilyMeasure_image k q.1
        (((C q.1).branch q.2).measurableSet_image (hQ q) (hQsource q)),
        ((C q.1).branch q.2).measure_image hh (hQ q) (hQsource q)]
      apply lintegral_congr_ae
      exact ae_restrict_of_forall_mem (hQ q) (fun y hy => (hj q hy.2).symm)
    _ = ∫⁻ y in S, j y ∂mainWallMeasure h := by
      rw [hdecomp, lintegral_iUnion hQ hdisjoint]

end AxisWallAtlasFamily

/-- The actual first return on an injectively represented finite section family has exact global transport. -/
theorem exists_axisFamily_firstReturn {ι : Type*} [Finite ι] [Encodable ι] [Nonempty ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι] (B : ι → NormalizedSymmetry)
    {k ε : ι → ℝ} {t₀ : ℝ} {E : ι → Set SectionCoordinates}
    (hk : ∀ i, 0 < k i) (hε : ∀ i, 0 < ε i)
    (hbound : ∀ i, ∀ z ∈ E i, mainWallChart (k i) z 0 ≤ -ε i)
    (hE : ∀ i, MeasurableSet (E i)) (hcharts : InjOn (axisFamilyChart B k) (axisFamilySection E)) :
    ∃ (R : ι × SectionCoordinates → ι × SectionCoordinates) (j : ι × SectionCoordinates → ℝ≥0∞),
      Measurable R ∧ Measurable j ∧ InjOn R (axisFamilyReturnDomain B k t₀ E) ∧
      (∀ z ∈ axisFamilyReturnDomain B k t₀ E, ∃ t,
        IsLeast (axisFamilyReturnTimes B k t₀ E z) t ∧
        axisFamilyChart B k (R z) = normalizedMaxCurve (axisFamilyChart B k z) t₀ t ∧
        R z ∈ axisFamilySection E) ∧
      (∀ z ∈ axisFamilyReturnDomain B k t₀ E, 1 < j z ∧ j z < ∞) ∧
      ∀ S, MeasurableSet S → S ⊆ axisFamilyReturnDomain B k t₀ E →
        MeasurableSet (R '' S) ∧ axisFamilyMeasure k (R '' S) = ∫⁻ z in S, j z ∂axisFamilyMeasure k := by
  classical
  obtain ⟨C, R, hR, hinj, hpiecesR, hcover, hfirst⟩ :=
    exists_axisFamily_firstReturnMap B (t₀ := t₀) hk hε hbound hE hcharts
  have hjlocal (i : ι) := (C i).exists_measurable_firstPiece_jacobian
    (I := Ioi t₀) (hk i) hk hE measurableSet_Ioi
  choose J hJ hpiecesJ using hjlocal
  let j : ι × SectionCoordinates → ℝ≥0∞ := fun z => J z.1 z.2
  have hj : Measurable j := measurable_from_prod_countable_right hJ
  have hcoverD (i : ι) : Prod.mk i ⁻¹' axisFamilyReturnDomain B k t₀ E ⊆
      ⋃ q, (C i).firstPiece E (Ioi t₀) q := fun _ hy => hcover i ▸ hy.2
  refine ⟨R, j, hR, hj, hinj, hfirst, ?_, ?_⟩
  · intro z hz
    obtain ⟨q, hq⟩ := mem_iUnion.mp (hcoverD z.1 hz)
    change 1 < J z.1 z.2 ∧ J z.1 z.2 < ∞
    rw [hpiecesJ z.1 q hq]
    exact ⟨ENNReal.one_lt_ofReal.mpr ((((C z.1) q.1).branch q.2).jacobian_gt_one
      (hk z.1) (hk q.1) hq.1.1 hq.1.2.1), ENNReal.ofReal_lt_top⟩
  · intro S hS hSD
    apply axisFamily_measure_image_of_fibers k hinj _ hS hSD
    intro i T hT hTD
    have hinji : InjOn (fun y => R (i, y)) (Prod.mk i ⁻¹' axisFamilyReturnDomain B k t₀ E) := by
      intro x hx y hy heq
      exact congrArg Prod.snd (hinj hx hy heq)
    exact (C i).measure_image_of_firstPieces (hk i) hE measurableSet_Ioi (hcoverD i) hinji
      (hpiecesR i) (hpiecesJ i) hT hTD

/-- For the three dominant-axis sections, physical chart injectivity is a proved geometric fact. -/
theorem exists_primaryAxis_firstReturn {h t₀ : ℝ} {ε : Fin 3 → ℝ} {E : Fin 3 → Set SectionCoordinates}
    (hh : 0 < h) (hε : ∀ i, 0 < ε i)
    (hbound : ∀ i, ∀ z ∈ E i, mainWallChart h z 0 ≤ -ε i)
    (hE : ∀ i, MeasurableSet (E i)) (hdom : ∀ i, E i ⊆ dominantWallChartDomain h) :
    ∃ (R : Fin 3 × SectionCoordinates → Fin 3 × SectionCoordinates)
      (j : Fin 3 × SectionCoordinates → ℝ≥0∞),
      Measurable R ∧ Measurable j ∧ InjOn R (axisFamilyReturnDomain primaryAxisFrame (fun _ => h) t₀ E) ∧
      (∀ z ∈ axisFamilyReturnDomain primaryAxisFrame (fun _ => h) t₀ E, ∃ t,
        IsLeast (axisFamilyReturnTimes primaryAxisFrame (fun _ => h) t₀ E z) t ∧
        axisFamilyChart primaryAxisFrame (fun _ => h) (R z) =
          normalizedMaxCurve (axisFamilyChart primaryAxisFrame (fun _ => h) z) t₀ t ∧
        R z ∈ axisFamilySection E) ∧
      (∀ z ∈ axisFamilyReturnDomain primaryAxisFrame (fun _ => h) t₀ E, 1 < j z ∧ j z < ∞) ∧
      ∀ S, MeasurableSet S → S ⊆ axisFamilyReturnDomain primaryAxisFrame (fun _ => h) t₀ E →
        MeasurableSet (R '' S) ∧ axisFamilyMeasure (fun _ : Fin 3 => h) (R '' S) =
          ∫⁻ z in S, j z ∂axisFamilyMeasure (fun _ : Fin 3 => h) :=
  exists_axisFamily_firstReturn primaryAxisFrame (fun _ => hh) hε hbound hE (primaryAxisChart_injOn hdom)

end BianchiIX
