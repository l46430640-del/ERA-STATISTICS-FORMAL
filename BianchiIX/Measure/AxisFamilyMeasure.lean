import BianchiIX.Measure.AxisArrivalMeasure
import Mathlib.MeasureTheory.MeasurableSpace.Prod

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal

/-- The sum of the verified coordinate flux measures on labelled section charts. -/
def axisFamilyMeasure {ι : Type*} [MeasurableSpace ι] (k : ι → ℝ) : Measure (ι × SectionCoordinates) :=
  Measure.sum (fun i => (mainWallMeasure (k i)).map (Prod.mk i))

theorem axisFamilyMeasure_apply {ι : Type*} [MeasurableSpace ι] (k : ι → ℝ)
    {S : Set (ι × SectionCoordinates)} (hS : MeasurableSet S) :
    axisFamilyMeasure k S = ∑' i, mainWallMeasure (k i) (Prod.mk i ⁻¹' S) := by
  rw [axisFamilyMeasure, Measure.sum_apply _ hS]
  exact tsum_congr (fun _ => Measure.map_apply measurable_prodMk_left hS)

theorem axisFamilyMeasure_image {ι : Type*} [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (k : ι → ℝ) (i : ι) {S : Set SectionCoordinates} (hS : MeasurableSet S) :
    axisFamilyMeasure k (Prod.mk i '' S) = mainWallMeasure (k i) S := by
  classical
  rw [axisFamilyMeasure_apply k ((measurableEmbedding_prodMk_left i).measurableSet_image.mpr hS)]
  have hpre (j : ι) : Prod.mk j ⁻¹' (Prod.mk i '' S) = if j = i then S else ∅ := by
    by_cases hji : j = i
    · subst j
      ext y
      simp
    · ext y
      simp [hji, Ne.symm hji]
  simp [hpre, apply_ite]

theorem lintegral_axisFamilyMeasure {ι : Type*} [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (k : ι → ℝ) (f : ι × SectionCoordinates → ℝ≥0∞) :
    (∫⁻ z, f z ∂axisFamilyMeasure k) = ∑' i, ∫⁻ y, f (i, y) ∂mainWallMeasure (k i) := by
  rw [axisFamilyMeasure, lintegral_sum_measure]
  exact tsum_congr (fun i => (measurableEmbedding_prodMk_left i).lintegral_map f)

theorem setLIntegral_axisFamilyMeasure {ι : Type*} [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (k : ι → ℝ) {S : Set (ι × SectionCoordinates)} (hS : MeasurableSet S)
    (f : ι × SectionCoordinates → ℝ≥0∞) :
    (∫⁻ z in S, f z ∂axisFamilyMeasure k) =
      ∑' i, ∫⁻ y in Prod.mk i ⁻¹' S, f (i, y) ∂mainWallMeasure (k i) := by
  rw [← lintegral_indicator hS, lintegral_axisFamilyMeasure]
  apply tsum_congr
  intro i
  rw [← lintegral_indicator (hS.preimage measurable_prodMk_left)]
  rfl

/-- Injectivity lets exact image formulas on the individual source fibers be summed. -/
theorem axisFamily_measure_image_of_fibers {ι : Type*} [Countable ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] (k : ι → ℝ)
    {R : ι × SectionCoordinates → ι × SectionCoordinates} {j : ι × SectionCoordinates → ℝ≥0∞}
    {D S : Set (ι × SectionCoordinates)} (hinj : InjOn R D)
    (hlocal : ∀ i, ∀ T : Set SectionCoordinates, MeasurableSet T → T ⊆ Prod.mk i ⁻¹' D →
      MeasurableSet ((fun y => R (i, y)) '' T) ∧
        axisFamilyMeasure k ((fun y => R (i, y)) '' T) = ∫⁻ y in T, j (i, y) ∂mainWallMeasure (k i))
    (hS : MeasurableSet S) (hSD : S ⊆ D) :
    MeasurableSet (R '' S) ∧ axisFamilyMeasure k (R '' S) = ∫⁻ z in S, j z ∂axisFamilyMeasure k := by
  let Q (i : ι) := (fun y => R (i, y)) '' (Prod.mk i ⁻¹' S)
  have hQ (i : ι) := hlocal i (Prod.mk i ⁻¹' S) (hS.preimage measurable_prodMk_left)
    (fun _ hy => hSD hy)
  have hdisjoint : Pairwise (fun i l => Disjoint (Q i) (Q l)) := by
    intro i l hil
    rw [disjoint_left]
    rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, heq⟩
    exact hil (congrArg Prod.fst (hinj (hSD hx) (hSD hy) heq.symm))
  have hdecomp : R '' S = ⋃ i, Q i := by
    ext z
    constructor
    · rintro ⟨⟨i, y⟩, hy, rfl⟩
      exact mem_iUnion.mpr ⟨i, y, hy, rfl⟩
    · intro hz
      obtain ⟨i, y, hy, rfl⟩ := mem_iUnion.mp hz
      exact ⟨(i, y), hy, rfl⟩
  refine ⟨hdecomp ▸ MeasurableSet.iUnion (fun i => (hQ i).1), ?_⟩
  rw [hdecomp, measure_iUnion hdisjoint (fun i => (hQ i).1), setLIntegral_axisFamilyMeasure k hS j]
  exact tsum_congr (fun i => (hQ i).2)

end BianchiIX
