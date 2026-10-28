import BianchiIX.Dynamics.AxisWallFlowMap
import BianchiIX.Measure.TransverseWallNull

noncomputable section

namespace BianchiIX

open Set Filter MeasureTheory
open scoped Topology

theorem axisWallOrbitSaturation_eq_image (A : NormalizedSymmetry) {h : ℝ}
    {Z : Set SectionCoordinates} (hZ : Z ⊆ mainWallChartDomain h) :
    normalizedOrbitSaturation (axisWallChart A h '' Z) =
      axisWallFlowMap A h '' ((Prod.fst ⁻¹' Z) ∩ axisWallFlowDomain A h) := by
  ext x
  constructor
  · rintro ⟨_, ⟨z, hz, rfl⟩, t, ht, rfl⟩
    exact ⟨(z, t), ⟨hz, hZ hz, ht⟩, rfl⟩
  · rintro ⟨p, ⟨hz, hp⟩, rfl⟩
    exact ⟨axisWallChart A h p.1, mem_image_of_mem _ hz, p.2, hp.2, rfl⟩

/-- The exact wall orbit map sends every Borel subset of its domain to a Borel set. -/
theorem measurableSet_axisWallFlowMap_image (A : NormalizedSymmetry) {h : ℝ}
    (hh : 0 < h) {S : Set (SectionCoordinates × ℝ)} (hS : MeasurableSet S)
    (hdom : S ⊆ axisWallFlowDomain A h) : MeasurableSet (axisWallFlowMap A h '' S) := by
  classical
  by_cases hne : S.Nonempty
  · let : Nonempty S := hne.to_subtype
    choose V hVo hpV hVD hVinj using
      (fun p : S => exists_axisWallFlowMap_injOn A hh (hdom p.property))
    obtain ⟨f, hf⟩ := (HereditarilyLindelofSpace.isLindelof S).indexed_countable_subcover V hVo
      (fun p hp => mem_iUnion.mpr ⟨⟨p, hp⟩, hpV ⟨p, hp⟩⟩)
    have heq : axisWallFlowMap A h '' S = ⋃ n : ℕ, axisWallFlowMap A h '' (S ∩ V (f n)) := by
      ext x
      constructor
      · rintro ⟨p, hp, rfl⟩
        obtain ⟨n, hn⟩ := mem_iUnion.mp (hf hp)
        exact mem_iUnion.mpr ⟨n, p, ⟨hp, hn⟩, rfl⟩
      · rintro hx
        obtain ⟨n, p, hp, rfl⟩ := mem_iUnion.mp hx
        exact mem_image_of_mem _ hp.1
    rw [heq]
    apply MeasurableSet.iUnion
    intro n
    exact (hS.inter (hVo (f n)).measurableSet).image_of_continuousOn_injOn
      (fun p hp => (contDiffAt_axisWallFlowMap A (hdom hp.1)).continuousAt.continuousWithinAt)
      ((hVinj (f n)).mono inter_subset_right)
  · rw [Set.not_nonempty_iff_eq_empty.mp hne, image_empty]
    exact MeasurableSet.empty

/-- Local injectivity gives a Borel saturation, including all existing negative times. -/
theorem measurableSet_axisWallOrbitSaturation (A : NormalizedSymmetry) {h : ℝ}
    (hh : 0 < h) {Z : Set SectionCoordinates} (hchart : Z ⊆ mainWallChartDomain h)
    (hZ : MeasurableSet Z) : MeasurableSet (normalizedOrbitSaturation (axisWallChart A h '' Z)) := by
  rw [axisWallOrbitSaturation_eq_image A hchart]
  exact measurableSet_axisWallFlowMap_image A hh
    ((hZ.preimage measurable_fst).inter (isOpen_axisWallFlowDomain A h).measurableSet)
    inter_subset_right

theorem axisWallOrbitSaturation_physical (A : NormalizedSymmetry) {h : ℝ}
    (hh : 0 < h) {Z : Set SectionCoordinates} (hchart : Z ⊆ mainWallChartDomain h)
    {x : NormalizedState} (hx : x ∈ normalizedOrbitSaturation (axisWallChart A h '' Z)) :
    positiveWalls x ∧ stateConstraint x = 1 := by
  obtain ⟨_, ⟨z, hz, rfl⟩, t, ht, rfl⟩ := hx
  exact (maximalNormalizedSolution (axisWallChart A h z) 0).physical
    (axisWallChart_positive A hh z) (axisWallChart_constraint A (hchart hz)) ht

theorem preimage_axisWallOrbitSaturation (A : NormalizedSymmetry) (C : SectionCoordinates → NormalizedState)
    (h : ℝ) (Z : Set SectionCoordinates) :
    C ⁻¹' normalizedOrbitSaturation (axisWallChart A h '' Z) = transverseAxisWallOrbitPreimage C A h 0 Z := by
  ext y
  constructor
  · rintro ⟨_, ⟨z, hz, rfl⟩, t, ht, heq⟩
    have H := normalizedMaxCurve_inverse ht
    rw [heq] at H
    exact ⟨-t, H.1, z, hz, H.2.symm⟩
  · rintro ⟨t, ht, z, hz, heq⟩
    have H := normalizedMaxCurve_inverse ht
    rw [← heq] at H
    exact ⟨axisWallChart A h z, mem_image_of_mem _ hz, -t, H.1, H.2⟩

/-- The same ambient saturation is null on every transverse initial chart. -/
theorem volume_preimage_axisWallOrbitSaturation (A : NormalizedSymmetry) {h : ℝ}
    {C : SectionCoordinates → NormalizedState} {U : Set SectionCoordinates}
    (hh : 0 < h) (hU : IsOpen U) (hC : ∀ y ∈ U, ContDiffAt ℝ 1 C y)
    (hp : ∀ y ∈ U, positiveWalls (C y)) (hc : ∀ y ∈ U, stateConstraint (C y) = 1)
    (hflux : ∀ y ∈ U,
      normalizedSectionFlux (C y) (fun i => fderiv ℝ C y (Pi.single i 1)) ≠ 0)
    {Z : Set SectionCoordinates} (hchart : Z ⊆ mainWallChartDomain h) (hZ : volume Z = 0) :
    volume (U ∩ C ⁻¹' normalizedOrbitSaturation (axisWallChart A h '' Z)) = 0 := by
  rw [preimage_axisWallOrbitSaturation]
  exact volume_transverseAxisWallOrbitPreimage A hh hU hC hp hc hflux hchart hZ

end BianchiIX
