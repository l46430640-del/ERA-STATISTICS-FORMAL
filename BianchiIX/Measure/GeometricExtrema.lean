import BianchiIX.Measure.GeometricSectionLimit
import BianchiIX.Dynamics.TaubExtrema

noncomputable section

namespace BianchiIX

open Set Filter MeasureTheory
open scoped ENNReal

theorem exists_axis_extrema_of_not_mem_geometricException
    (hBrehm : Literature.BrehmIXAttractorInput) {x : NormalizedState}
    (hx : x ∈ physicalPhaseSpace) (hN : x ∉ geometricException) :
    ∃ i : Fin 3,
      limsup (fun t => wallValue i (normalizedMaxCurve x 0 t)) atTop = 1 ∧
      limsup (fun t => normalizedMaxWall (normalizedMaxCurve x 0 t)) atTop = 1 ∧
      liminf (fun t => shearSq (normalizedMaxCurve x 0 t 0) (normalizedMaxCurve x 0 t 1)) atTop = 0 := by
  obtain ⟨i, Hi⟩ := exists_axis_arc_limits_of_not_mem_geometricException hBrehm hx hN
  have hprod := hBrehm.wallProductDecay hx (fun hT => hN ⟨hx, Or.inl hT⟩)
  exact ⟨i, taub_arc_center_extrema i hx.2 hprod (Hi 0 (by constructor <;> norm_num))⟩

theorem ae_axis_extrema
    (hBirkhoff : Literature.BirkhoffErgodicInput ℝ)
    (hBrehm : Literature.BrehmIXAttractorInput)
    {C : SectionCoordinates → NormalizedState} {U : Set SectionCoordinates}
    (hU : IsOpen U) (hC : ∀ y ∈ U, ContDiffAt ℝ 1 C y)
    (hp : ∀ y ∈ U, positiveWalls (C y)) (hc : ∀ y ∈ U, stateConstraint (C y) = 1)
    (hflux : ∀ y ∈ U,
      normalizedSectionFlux (C y) (fun i => fderiv ℝ C y (Pi.single i 1)) ≠ 0) :
    ∀ᵐ y ∂volume, y ∈ U → ∃ i : Fin 3,
      limsup (fun t => wallValue i (normalizedMaxCurve (C y) 0 t)) atTop = 1 ∧
      limsup (fun t => normalizedMaxWall (normalizedMaxCurve (C y) 0 t)) atTop = 1 ∧
      liminf (fun t => shearSq (normalizedMaxCurve (C y) 0 t 0) (normalizedMaxCurve (C y) 0 t 1)) atTop = 0 := by
  have hn : ∀ᵐ y ∂volume, y ∉ U ∩ C ⁻¹' geometricException := by
    rw [ae_iff]
    simpa only [not_not, Set.ofPred_mem_eq] using
      volume_preimage_geometricException hBirkhoff hBrehm hU hC hp hc hflux
  filter_upwards [hn] with y hy hyU
  exact exists_axis_extrema_of_not_mem_geometricException hBrehm
    ⟨hp y hyU, hc y hyU⟩ (fun hG => hy ⟨hyU, hG⟩)

theorem ae_wall_shear_extrema
    (hBirkhoff : Literature.BirkhoffErgodicInput ℝ)
    (hBrehm : Literature.BrehmIXAttractorInput)
    {C : SectionCoordinates → NormalizedState} {U : Set SectionCoordinates}
    (hU : IsOpen U) (hC : ∀ y ∈ U, ContDiffAt ℝ 1 C y)
    (hp : ∀ y ∈ U, positiveWalls (C y)) (hc : ∀ y ∈ U, stateConstraint (C y) = 1)
    (hflux : ∀ y ∈ U,
      normalizedSectionFlux (C y) (fun i => fderiv ℝ C y (Pi.single i 1)) ≠ 0) :
    ∀ᵐ y ∂volume, y ∈ U →
      limsup (fun t => normalizedMaxWall (normalizedMaxCurve (C y) 0 t)) atTop = 1 ∧
      liminf (fun t => shearSq (normalizedMaxCurve (C y) 0 t 0) (normalizedMaxCurve (C y) 0 t 1)) atTop = 0 := by
  filter_upwards [ae_axis_extrema hBirkhoff hBrehm hU hC hp hc hflux] with y hy hyU
  obtain ⟨_, _, H⟩ := hy hyU
  exact H

theorem ae_axis_extrema_withDensity
    (hBirkhoff : Literature.BirkhoffErgodicInput ℝ)
    (hBrehm : Literature.BrehmIXAttractorInput)
    {C : SectionCoordinates → NormalizedState} {U : Set SectionCoordinates}
    (hU : IsOpen U) (hC : ∀ y ∈ U, ContDiffAt ℝ 1 C y)
    (hp : ∀ y ∈ U, positiveWalls (C y)) (hc : ∀ y ∈ U, stateConstraint (C y) = 1)
    (hflux : ∀ y ∈ U,
      normalizedSectionFlux (C y) (fun i => fderiv ℝ C y (Pi.single i 1)) ≠ 0)
    (ρ : SectionCoordinates → ℝ≥0∞) :
    ∀ᵐ y ∂(volume.withDensity ρ), y ∈ U → ∃ i : Fin 3,
      limsup (fun t => wallValue i (normalizedMaxCurve (C y) 0 t)) atTop = 1 ∧
      limsup (fun t => normalizedMaxWall (normalizedMaxCurve (C y) 0 t)) atTop = 1 ∧
      liminf (fun t => shearSq (normalizedMaxCurve (C y) 0 t 0) (normalizedMaxCurve (C y) 0 t 1)) atTop = 0 :=
  (withDensity_absolutelyContinuous volume ρ).ae_le
    (ae_axis_extrema hBirkhoff hBrehm hU hC hp hc hflux)

end BianchiIX
