import BianchiIX.Measure.AxisFirstMap
import BianchiIX.Measure.AxisReturnInjectivity

noncomputable section

namespace BianchiIX

open Set MeasureTheory

/-- Assemble the source charts into an actual measurable first return on the physical section family. -/
theorem exists_axisFamily_firstReturnMap {ι : Type*} [Finite ι] [Encodable ι] [Nonempty ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι] (B : ι → NormalizedSymmetry)
    {k ε : ι → ℝ} {t₀ : ℝ} {E : ι → Set SectionCoordinates}
    (hk : ∀ i, 0 < k i) (hε : ∀ i, 0 < ε i)
    (hbound : ∀ i, ∀ z ∈ E i, mainWallChart (k i) z 0 ≤ -ε i)
    (hE : ∀ i, MeasurableSet (E i)) (hcharts : InjOn (axisFamilyChart B k) (axisFamilySection E)) :
    ∃ (C : ∀ i, AxisWallAtlasFamily (B i) B (k i) k t₀)
      (R : ι × SectionCoordinates → ι × SectionCoordinates),
      Measurable R ∧ InjOn R (axisFamilyReturnDomain B k t₀ E) ∧
      (∀ i q, EqOn (fun y => R (i, y))
        (fun y => (q.1, (((C i) q.1).branch q.2).map y)) ((C i).firstPiece E (Ioi t₀) q)) ∧
      (∀ i, axisFamilyHittingDomain (B i) B (k i) k t₀ E (Ioi t₀) =
        ⋃ q, (C i).firstPiece E (Ioi t₀) q) ∧
      ∀ z ∈ axisFamilyReturnDomain B k t₀ E, ∃ t,
        IsLeast (axisFamilyReturnTimes B k t₀ E z) t ∧
        axisFamilyChart B k (R z) = normalizedMaxCurve (axisFamilyChart B k z) t₀ t ∧
        R z ∈ axisFamilySection E := by
  classical
  have hlocal (i : ι) := exists_axisFamily_firstMap (B i) B (t₀ := t₀) (hk i) hk hε
    (show Ioi t₀ ⊆ Ici t₀ from fun x hx => show t₀ ≤ x from le_of_lt hx) hbound hE measurableSet_Ioi
  choose C r hr hpieces hcover hfirst using hlocal
  let R : ι × SectionCoordinates → ι × SectionCoordinates := fun z => r z.1 z.2
  have hR : Measurable R := measurable_from_prod_countable_right hr
  have hspec : ∀ z ∈ axisFamilyReturnDomain B k t₀ E, ∃ t,
      IsLeast (axisFamilyReturnTimes B k t₀ E z) t ∧
      axisFamilyChart B k (R z) = normalizedMaxCurve (axisFamilyChart B k z) t₀ t ∧
      R z ∈ axisFamilySection E := by
    intro z hz
    obtain ⟨t, ht, hrel, hcoord, htarget⟩ := hfirst z.1 z.2 hz.2
    refine ⟨t, ht, ?_, htarget⟩
    change axisWallChart (B (r z.1 z.2).1) (k (r z.1 z.2).1) (r z.1 z.2).2 = _
    rw [hcoord]
    exact axisWallArrivalRelation_chart (B z.1) (B (r z.1 z.2).1) (hk z.1) hrel
  exact ⟨C, R, hR, axisFamily_firstReturn_injOn B hk hcharts
    (fun z hz => let ⟨t, ht, hstate, _⟩ := hspec z hz; ⟨t, ht, hstate⟩), hpieces, hcover, hspec⟩

end BianchiIX
