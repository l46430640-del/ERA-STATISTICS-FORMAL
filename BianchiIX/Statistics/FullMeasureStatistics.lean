import BianchiIX.Statistics.CommonPhysicalEraSequence
import BianchiIX.Statistics.PhysicalEraObservables
import BianchiIX.Statistics.ConstraintVolumeStatistics
import BianchiIX.Statistics.EraConsequences

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal

/-- The full-measure physical era theorem with all auxiliary choices internal and arbitrary chart densities. -/
theorem exists_full_measure_era_statistics
    (hBirkhoff : Literature.BirkhoffErgodicInput ℝ)
    (hBrehm : Literature.BrehmIXAttractorInput) :
    ∃ η ∈ Ioc (0 : ℝ) (1 / 40000),
      ∃ N : Set NormalizedState, MeasurableSet N ∧ N ⊆ physicalPhaseSpace ∧
        geometricException ⊆ N ∧
        (∀ x : NormalizedState, ∀ s ∈ normalizedMaxDomain x 0,
          normalizedMaxCurve x 0 s ∈ N ↔ x ∈ N) ∧
        (∀ (C : SectionCoordinates → NormalizedState) (U : Set SectionCoordinates),
          IsOpen U → (∀ y ∈ U, ContDiffAt ℝ 1 C y) →
          (∀ y ∈ U, positiveWalls (C y)) → (∀ y ∈ U, stateConstraint (C y) = 1) →
          (∀ y ∈ U, normalizedSectionFlux (C y) (fun i => fderiv ℝ C y (Pi.single i 1)) ≠ 0) →
          ∀ ρ : SectionCoordinates → ℝ≥0∞, (volume.withDensity ρ) (U ∩ C ⁻¹' N) = 0) ∧
        (∀ (C : FourCoordinates → NormalizedState) (U : Set FourCoordinates),
          (∀ y ∈ U, ContDiffAt ℝ 1 C y) →
          (∀ y ∈ U, normalizedConstraintVolume (C y)
            (fun i => fderiv ℝ C y (Pi.single i 1)) ≠ 0) →
          ∀ ρ : FourCoordinates → ℝ≥0∞, (volume.withDensity ρ) (U ∩ C ⁻¹' N) = 0) ∧
        ∃ K : ↥(physicalPhaseSpace \ N) → ℕ → ℕ+, Measurable K ∧
        ∃ Y : ↥(physicalPhaseSpace \ N) → ℕ → CoreAngleState, Measurable Y ∧
        ∃ t : ↥(physicalPhaseSpace \ N) → ℕ → ℝ, Measurable t ∧
        ∃ a : ↥(physicalPhaseSpace \ N) → ℕ → Fin 6, Measurable a ∧
          ∀ x, PhysicalEraSequence η 45 x.val (K x) (Y x) (t x) (a x) ∧
            ∀ n, let z := toProjectiveState ((axisFrame (a x n)).map
                (normalizedMaxCurve x.val 0 (t x n)))
              z 2 = 1 ∧ Real.sqrt ((z 0 - 1) ^ 2 + 1) = Y x n 0 ∧
                1 < Y x n 0 / 2 ∧ 2 / Y x n 0 ∈ Ioo (0 : ℝ) 1 ∧
                (K x n : ℕ) = Nat.floor (Y x n 0 / 2) := by
  obtain ⟨δ, hδ, hδmax, Hδ⟩ := exists_common_physical_era_sequence hBirkhoff hBrehm
  obtain ⟨N, hNm, hNp, hNg, hNi, hNn, hNfour, K, hK, Y, hY, t, ht, a, ha, H⟩ :=
    Hδ δ hδ le_rfl 45 (by norm_num) (1 / 400) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨δ, ⟨hδ, hδmax⟩, N, hNm, hNp, hNg, hNi, ?_, ?_,
    K, hK, Y, hY, t, ht, a, ha, fun x => ⟨H x, (H x).entrance_observables⟩⟩
  · intro C U hU hC hp hc hflux ρ
    exact withDensity_absolutelyContinuous volume ρ (hNn C U hU hC hp hc hflux)
  · intro C U hC hv ρ
    exact withDensity_absolutelyContinuous volume ρ (hNfour.preimage_constraint hC hv)

end BianchiIX
