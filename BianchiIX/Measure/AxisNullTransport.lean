import BianchiIX.Measure.AxisHitting
import BianchiIX.Dynamics.AxisFamilySections

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal

theorem AxisWallArrival.eligible_null {A B : NormalizedSymmetry} {h k t₀ : ℝ}
    (P : AxisWallArrival A B h k t₀) (hh : 0 < h) (hk : 0 < k)
    {Z : Set SectionCoordinates} {I : Set ℝ}
    (hZ : MeasurableSet Z) (hI : MeasurableSet I) (hnull : mainWallMeasure k Z = 0) :
    mainWallMeasure h (P.eligible Z I) = 0 := by
  apply (P.measure_image_null_iff hh hk (P.measurableSet_eligible hZ hI) (fun _ hx => hx.1)).mp
  exact measure_mono_null (by rintro _ ⟨x, hx, rfl⟩; exact hx.2.2) hnull

/-- The countable arrival atlas handles all actual times simultaneously. -/
theorem axisFamilyHittingDomain_null {ι : Type*} [Countable ι]
    (A : NormalizedSymmetry) (B : ι → NormalizedSymmetry) {h t₀ : ℝ} {k : ι → ℝ}
    (hh : 0 < h) (hk : ∀ i, 0 < k i) {Z : ι → Set SectionCoordinates} {I : Set ℝ}
    (hZ : ∀ i, MeasurableSet (Z i)) (hI : MeasurableSet I)
    (hnull : ∀ i, mainWallMeasure (k i) (Z i) = 0) :
    mainWallMeasure h (axisFamilyHittingDomain A B h k t₀ Z I) = 0 := by
  obtain ⟨C⟩ := exists_axisWallAtlasFamily A B (t₀ := t₀) hh hk
  rw [C.hittingDomain_eq_iUnion Z I]
  exact measure_iUnion_null fun i => measure_iUnion_null fun n =>
    ((C i).branch n).eligible_null hh (hk i) (hZ i) hI (hnull i)

/-- Intersections with the actual orbit, at any time in its maximal domain. -/
def axisFamilyOrbitPreimage {ι : Type*} (A : NormalizedSymmetry) (B : ι → NormalizedSymmetry)
    (h : ℝ) (k : ι → ℝ) (t₀ : ℝ) (Z : ι → Set SectionCoordinates) : Set SectionCoordinates :=
  {y | y ∈ mainWallChartDomain h ∧
    ∃ t ∈ normalizedMaxDomain (axisWallChart A h y) t₀, ∃ i, ∃ z ∈ Z i,
      axisWallChart (B i) (k i) z = normalizedMaxCurve (axisWallChart A h y) t₀ t}

theorem axisFamilyOrbitPreimage_eq_hittingDomain {ι : Type*}
    (A : NormalizedSymmetry) (B : ι → NormalizedSymmetry) {h t₀ : ℝ} {k : ι → ℝ}
    (hh : 0 < h) {Z : ι → Set SectionCoordinates}
    (hchart : ∀ i, Z i ⊆ mainWallChartDomain (k i)) :
    axisFamilyOrbitPreimage A B h k t₀ Z = axisFamilyHittingDomain A B h k t₀ Z univ := by
  ext y
  constructor
  · rintro ⟨hy, t, ht, i, z, hz, heq⟩
    refine ⟨t, mem_univ _, i, ⟨hy, ht, ?_, ?_⟩, ?_⟩
    · rw [← heq, axisWallChart, ContinuousLinearEquiv.apply_symm_apply]
      rfl
    · rw [← heq, axisWallChart, ContinuousLinearEquiv.apply_symm_apply]
      exact mainWallChart_negative (hchart i hz)
    · rw [← heq, axisWallCoordinates_chart]
      exact hz
  · rintro ⟨t, _, i, hrel, hz⟩
    exact ⟨hrel.1, t, hrel.2.1, i,
      axisWallCoordinates (B i) (normalizedMaxCurve (axisWallChart A h y) t₀ t), hz,
      axisWallArrivalRelation_chart A (B i) hh hrel⟩

theorem axisFamilyOrbitPreimage_measurable_null {ι : Type*} [Countable ι]
    (A : NormalizedSymmetry) (B : ι → NormalizedSymmetry) {h t₀ : ℝ} {k : ι → ℝ}
    (hh : 0 < h) (hk : ∀ i, 0 < k i) {Z : ι → Set SectionCoordinates}
    (hchart : ∀ i, Z i ⊆ mainWallChartDomain (k i)) (hZ : ∀ i, MeasurableSet (Z i))
    (hnull : ∀ i, mainWallMeasure (k i) (Z i) = 0) :
    MeasurableSet (axisFamilyOrbitPreimage A B h k t₀ Z) ∧
      mainWallMeasure h (axisFamilyOrbitPreimage A B h k t₀ Z) = 0 := by
  rw [axisFamilyOrbitPreimage_eq_hittingDomain A B hh hchart]
  exact ⟨measurableSet_axisFamilyHittingDomain A B hh hk hZ MeasurableSet.univ,
    axisFamilyHittingDomain_null A B hh hk hZ MeasurableSet.univ hnull⟩

theorem ae_axisWall_orbit_avoids_null_targets {ι : Type*} [Countable ι]
    (A : NormalizedSymmetry) (B : ι → NormalizedSymmetry) {h t₀ : ℝ} {k : ι → ℝ}
    (hh : 0 < h) (hk : ∀ i, 0 < k i) {Z : ι → Set SectionCoordinates}
    (hchart : ∀ i, Z i ⊆ mainWallChartDomain (k i)) (hZ : ∀ i, MeasurableSet (Z i))
    (hnull : ∀ i, mainWallMeasure (k i) (Z i) = 0) :
    ∀ᵐ y ∂mainWallMeasure h, y ∈ mainWallChartDomain h →
      ∀ t ∈ normalizedMaxDomain (axisWallChart A h y) t₀, ∀ i, ∀ z ∈ Z i,
        axisWallChart (B i) (k i) z ≠ normalizedMaxCurve (axisWallChart A h y) t₀ t := by
  have H := (axisFamilyOrbitPreimage_measurable_null A B (t₀ := t₀) hh hk hchart hZ hnull).2
  have ha : ∀ᵐ y ∂mainWallMeasure h, y ∉ axisFamilyOrbitPreimage A B h k t₀ Z := by
    simpa only [ae_iff, not_not, ofPred_mem_eq] using H
  filter_upwards [ha] with y hy hsource t ht i z hz heq
  exact hy ⟨hsource, t, ht, i, z, hz, heq⟩

theorem axisFamilyOrbitPreimage_volume_null {ι : Type*} [Countable ι]
    (A : NormalizedSymmetry) (B : ι → NormalizedSymmetry) {h t₀ : ℝ} {k : ι → ℝ}
    (hh : 0 < h) (hk : ∀ i, 0 < k i) {Z : ι → Set SectionCoordinates}
    (hchart : ∀ i, Z i ⊆ mainWallChartDomain (k i)) (hZ : ∀ i, MeasurableSet (Z i))
    (hnull : ∀ i, volume (Z i) = 0) :
    MeasurableSet (axisFamilyOrbitPreimage A B h k t₀ Z) ∧
      volume (axisFamilyOrbitPreimage A B h k t₀ Z) = 0 := by
  have hf (i : ι) : mainWallMeasure (k i) (Z i) = 0 := by
    apply (mainWallMeasure_null_iff (hk i) (Z i)).mpr
    rw [Measure.restrict_apply (hZ i), inter_eq_left.mpr (hchart i)]
    exact hnull i
  obtain ⟨hmeas, hzero⟩ := axisFamilyOrbitPreimage_measurable_null A B (t₀ := t₀) hh hk hchart hZ hf
  refine ⟨hmeas, ?_⟩
  have H := (mainWallMeasure_null_iff hh _).mp hzero
  rwa [Measure.restrict_apply hmeas, inter_eq_left.mpr (fun _ hy => hy.1)] at H

theorem axisFamilyOrbitPreimage_density_null {ι : Type*} [Countable ι]
    (A : NormalizedSymmetry) (B : ι → NormalizedSymmetry) {h t₀ : ℝ} {k : ι → ℝ}
    (hh : 0 < h) (hk : ∀ i, 0 < k i) {Z : ι → Set SectionCoordinates}
    (hchart : ∀ i, Z i ⊆ mainWallChartDomain (k i)) (hZ : ∀ i, MeasurableSet (Z i))
    (hnull : ∀ i, volume (Z i) = 0) (ρ : SectionCoordinates → ℝ≥0∞) :
    (volume.withDensity ρ) (axisFamilyOrbitPreimage A B h k t₀ Z) = 0 :=
  withDensity_absolutelyContinuous volume ρ
    (axisFamilyOrbitPreimage_volume_null A B hh hk hchart hZ hnull).2

end BianchiIX
