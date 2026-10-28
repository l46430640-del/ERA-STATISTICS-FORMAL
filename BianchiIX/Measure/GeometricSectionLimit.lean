import BianchiIX.Measure.GeometricException
import BianchiIX.Dynamics.TaubArcLimit

noncomputable section

namespace BianchiIX

open Set Filter MeasureTheory

/-- One physical axis supplies the boundary limit at every allowed fixed wall height. -/
theorem exists_axis_boundary_limits_of_not_mem_geometricException
    (hBrehm : Literature.BrehmIXAttractorInput) {x : NormalizedState}
    (hx : x ∈ physicalPhaseSpace) (hN : x ∉ geometricException) :
    ∃ i : Fin 3, taubPoint i ∈ normalizedOmegaLimit x ∧
      ∀ h : ℝ, 0 < h → h ≤ 1 / 16 → primaryAxisBoundary i h ∈ normalizedOmegaLimit x := by
  obtain ⟨hr, Hvisit⟩ := arbitrarily_late_taub_approach_of_not_mem_geometricException hx hN
  obtain ⟨i, hi⟩ := exists_fixed_late_taub_target Hvisit
  have hvisit := mem_normalizedOmegaLimit_of_late_visit hi
  have hprod := hBrehm.wallProductDecay hx (fun hT => hN ⟨hx, Or.inl hT⟩)
  refine ⟨i, hvisit, fun h hh hhmax => ?_⟩
  exact primaryAxisBoundary_mem_omegaLimit i hx.2 hx.1 (hr i) hh hhmax
    (div_pos hh (by norm_num) : 0 < h / 16) (by linarith only [hh]) hprod hvisit

theorem ae_axis_boundary_limits
    (hBirkhoff : Literature.BirkhoffErgodicInput ℝ)
    (hBrehm : Literature.BrehmIXAttractorInput)
    {C : SectionCoordinates → NormalizedState} {U : Set SectionCoordinates}
    (hU : IsOpen U) (hC : ∀ y ∈ U, ContDiffAt ℝ 1 C y)
    (hp : ∀ y ∈ U, positiveWalls (C y)) (hc : ∀ y ∈ U, stateConstraint (C y) = 1)
    (hflux : ∀ y ∈ U,
      normalizedSectionFlux (C y) (fun i => fderiv ℝ C y (Pi.single i 1)) ≠ 0) :
    ∀ᵐ y ∂volume, y ∈ U → ∃ i : Fin 3, taubPoint i ∈ normalizedOmegaLimit (C y) ∧
      ∀ h : ℝ, 0 < h → h ≤ 1 / 16 → primaryAxisBoundary i h ∈ normalizedOmegaLimit (C y) := by
  have hn : ∀ᵐ y ∂volume, y ∉ U ∩ C ⁻¹' geometricException := by
    rw [ae_iff]
    simpa only [not_not, Set.ofPred_mem_eq] using volume_preimage_geometricException hBirkhoff hBrehm hU hC hp hc hflux
  filter_upwards [hn] with y hy hyU
  exact exists_axis_boundary_limits_of_not_mem_geometricException hBrehm
    ⟨hp y hyU, hc y hyU⟩ (fun hG => hy ⟨hyU, hG⟩)

theorem exists_axis_arc_limits_of_not_mem_geometricException
    (hBrehm : Literature.BrehmIXAttractorInput) {x : NormalizedState}
    (hx : x ∈ physicalPhaseSpace) (hN : x ∉ geometricException) :
    ∃ i : Fin 3, ∀ q ∈ Icc (-1 : ℝ) 1, primaryAxisArc i q ∈ normalizedOmegaLimit x := by
  obtain ⟨i, _, H⟩ := exists_axis_boundary_limits_of_not_mem_geometricException hBrehm hx hN
  exact ⟨i, primaryAxisArc_closed_mem_omegaLimit_of_boundary i hx.2 (by norm_num) (by norm_num)
    (H (1 / 32) (by norm_num) (by norm_num))⟩

theorem ae_axis_arc_limits
    (hBirkhoff : Literature.BirkhoffErgodicInput ℝ)
    (hBrehm : Literature.BrehmIXAttractorInput)
    {C : SectionCoordinates → NormalizedState} {U : Set SectionCoordinates}
    (hU : IsOpen U) (hC : ∀ y ∈ U, ContDiffAt ℝ 1 C y)
    (hp : ∀ y ∈ U, positiveWalls (C y)) (hc : ∀ y ∈ U, stateConstraint (C y) = 1)
    (hflux : ∀ y ∈ U,
      normalizedSectionFlux (C y) (fun i => fderiv ℝ C y (Pi.single i 1)) ≠ 0) :
    ∀ᵐ y ∂volume, y ∈ U → ∃ i : Fin 3,
      ∀ q ∈ Icc (-1 : ℝ) 1, primaryAxisArc i q ∈ normalizedOmegaLimit (C y) := by
  filter_upwards [ae_axis_boundary_limits hBirkhoff hBrehm hU hC hp hc hflux] with y hy hyU
  obtain ⟨i, _, H⟩ := hy hyU
  exact ⟨i, primaryAxisArc_closed_mem_omegaLimit_of_boundary i (hc y hyU) (by norm_num) (by norm_num)
    (H (1 / 32) (by norm_num) (by norm_num))⟩

end BianchiIX
