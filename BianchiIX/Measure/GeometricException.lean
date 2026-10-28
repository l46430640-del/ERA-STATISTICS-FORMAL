import BianchiIX.Dynamics.EventualTaubSeparation
import BianchiIX.Literature.Attractor
import BianchiIX.Measure.TaubSubspaceNull
import BianchiIX.Measure.LateAwaySectionNull

noncomputable section

namespace BianchiIX

open Set Filter MeasureTheory
open scoped Topology

def geometricException : Set NormalizedState :=
  {x | x ∈ physicalPhaseSpace ∧ (x ∈ taubSubspaces ∨ EventuallyTaubSeparated x)}

theorem measurableSet_geometricException : MeasurableSet geometricException := by
  have heq : geometricException = (physicalPhaseSpace ∩ taubSubspaces) ∪
      {x | x ∈ physicalPhaseSpace ∧ EventuallyTaubSeparated x} := by
    ext x; simp [geometricException, and_or_left]
  rw [heq]
  exact (measurableSet_physicalPhaseSpace.inter isClosed_taubSubspaces.measurableSet).union
    measurableSet_physical_eventuallyTaubSeparated

theorem mem_geometricException_maxCurve_iff {x : NormalizedState} {t : ℝ}
    (ht : t ∈ normalizedMaxDomain x 0) :
    normalizedMaxCurve x 0 t ∈ geometricException ↔ x ∈ geometricException := by
  simp only [geometricException, mem_ofPred_eq, mem_physicalPhaseSpace_maxCurve_iff ht,
    mem_taubSubspaces_maxCurve_iff ht]
  apply and_congr_right
  intro hx
  rw [eventuallyTaubSeparated_maxCurve_iff hx.2 ht]

theorem volume_preimage_taubSubspaces
    {C : SectionCoordinates → NormalizedState} {U : Set SectionCoordinates}
    (hC : ∀ y ∈ U, ContDiffAt ℝ 1 C y)
    (hflux : ∀ y ∈ U,
      normalizedSectionFlux (C y) (fun i => fderiv ℝ C y (Pi.single i 1)) ≠ 0) :
    volume (U ∩ C ⁻¹' taubSubspaces) = 0 := by
  have heq : U ∩ C ⁻¹' taubSubspaces = ⋃ i : Fin 3,
      {y | y ∈ U ∧ normalizedTaubRadiusSq ((primaryAxisFrame i).map (C y)) = 0} := by
    ext y; simp [taubSubspaces, exists_and_left]
  rw [heq]
  exact measure_iUnion_null fun i => volume_axis_taub_subspace_section (primaryAxisFrame i) hC hflux

/-- The attractor input is used only to supply product decay outside the Taub spaces. -/
theorem volume_preimage_geometricException
    (hBirkhoff : Literature.BirkhoffErgodicInput ℝ)
    (hBrehm : Literature.BrehmIXAttractorInput)
    {C : SectionCoordinates → NormalizedState} {U : Set SectionCoordinates}
    (hU : IsOpen U) (hC : ∀ y ∈ U, ContDiffAt ℝ 1 C y)
    (hp : ∀ y ∈ U, positiveWalls (C y)) (hc : ∀ y ∈ U, stateConstraint (C y) = 1)
    (hflux : ∀ y ∈ U,
      normalizedSectionFlux (C y) (fun i => fderiv ℝ C y (Pi.single i 1)) ≠ 0) :
    volume (U ∩ C ⁻¹' geometricException) = 0 := by
  apply measure_mono_null (t := (U ∩ C ⁻¹' taubSubspaces) ∪
    {y | y ∈ U ∧ EventuallyTaubSeparated (C y) ∧ WallProductDecay (C y)}) _
    (measure_union_null (volume_preimage_taubSubspaces hC hflux)
      (volume_eventually_taub_separated_section hBirkhoff hU hC hp hc hflux))
  intro y hy
  by_cases hT : C y ∈ taubSubspaces
  · exact Or.inl ⟨hy.1, hT⟩
  · exact Or.inr ⟨hy.1, hy.2.2.resolve_left hT,
      hBrehm.wallProductDecay ⟨hp y hy.1, hc y hy.1⟩ hT⟩

theorem arbitrarily_late_taub_approach_of_not_mem_geometricException
    {x : NormalizedState} (hx : x ∈ physicalPhaseSpace) (hN : x ∉ geometricException) :
    (∀ i, 0 < normalizedTaubRadiusSq ((primaryAxisFrame i).map x)) ∧
      ∀ ε > (0 : ℝ), ∀ R : ℝ, ∃ t ≥ R, ∃ i : Fin 3,
        normalizedEuclideanDistance (normalizedMaxCurve x 0 t) (taubPoint i) < ε := by
  exact ⟨(not_mem_taubSubspaces_iff x).mp (fun hT => hN ⟨hx, Or.inl hT⟩),
    (not_eventuallyTaubSeparated_iff x).mp (fun hT => hN ⟨hx, Or.inr hT⟩)⟩

end BianchiIX
