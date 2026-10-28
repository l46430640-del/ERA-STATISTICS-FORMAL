import BianchiIX.Statistics.CommonCoreRestart

noncomputable section

namespace BianchiIX

open Set Filter MeasureTheory
open scoped Topology ENNReal

/-- Outside one Borel invariant set, every physical initial state reaches a statistical era core.
The exceptional set is null on every smooth transverse chart, not merely on the selected walls. -/
theorem exists_common_borel_statistical_exception
    (hBirkhoff : Literature.BirkhoffErgodicInput ℝ)
    (hBrehm : Literature.BrehmIXAttractorInput) :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 20 ≤ J → ∀ σ : ℝ, 0 < σ → σ < 1 → σ * (2 * J : ℕ) < 1 →
        ∃ Bcap > (0 : ℝ), Bcap < 1 ∧ ∃ N : Set NormalizedState,
          MeasurableSet N ∧ N ⊆ physicalPhaseSpace ∧
          (∀ x : NormalizedState, ∀ t ∈ normalizedMaxDomain x 0,
            normalizedMaxCurve x 0 t ∈ N ↔ x ∈ N) ∧
          (∀ (C : SectionCoordinates → NormalizedState) (U : Set SectionCoordinates),
            IsOpen U → (∀ y ∈ U, ContDiffAt ℝ 1 C y) →
            (∀ y ∈ U, positiveWalls (C y)) → (∀ y ∈ U, stateConstraint (C y) = 1) →
            (∀ y ∈ U, normalizedSectionFlux (C y) (fun i => fderiv ℝ C y (Pi.single i 1)) ≠ 0) →
            volume (U ∩ C ⁻¹' N) = 0) ∧ NullInFourCoordinates N ∧
          ∀ x ∈ physicalPhaseSpace, x ∉ N → StatisticalCoreFuture η J σ Bcap x := by
  obtain ⟨δ, hδ, hδmax, Hδ⟩ := exists_common_borel_core_restart hBirkhoff hBrehm
  refine ⟨δ, hδ, hδmax, ?_⟩
  intro η hη hηδ J hJ σ hσ hσone hσJ
  obtain ⟨Bcap, hcap, hcapone, HB⟩ :=
    Hδ η hη hηδ J hJ σ hσ hσone hσJ
  obtain ⟨N, hNm, hNp, _, hNi, hNn, hNfour, W, _, HW⟩ := HB Bcap hcap
  refine ⟨Bcap, hcap, hcapone, N, hNm, hNp, hNi, hNn, hNfour, ?_⟩
  intro x hx hn
  exact (HW x hx hn).2.statisticalCoreFuture

/-- No orbit-decay condition remains in the almost-everywhere conclusion. -/
theorem exists_transverse_statistics
    (hBirkhoff : Literature.BirkhoffErgodicInput ℝ)
    (hBrehm : Literature.BrehmIXAttractorInput) :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 20 ≤ J → ∀ σ : ℝ, 0 < σ → σ < 1 → σ * (2 * J : ℕ) < 1 →
        ∃ Bcap > (0 : ℝ), Bcap < 1 ∧
          ∀ (C : SectionCoordinates → NormalizedState) (U : Set SectionCoordinates),
            IsOpen U → (∀ y ∈ U, ContDiffAt ℝ 1 C y) →
            (∀ y ∈ U, positiveWalls (C y)) → (∀ y ∈ U, stateConstraint (C y) = 1) →
            (∀ y ∈ U, normalizedSectionFlux (C y) (fun i => fderiv ℝ C y (Pi.single i 1)) ≠ 0) →
            ∀ ρ : SectionCoordinates → ℝ≥0∞,
              ∀ᵐ y ∂(volume.withDensity ρ), y ∈ U → StatisticalCoreFuture η J σ Bcap (C y) := by
  obtain ⟨δ, hδ, hδmax, Hδ⟩ := exists_common_borel_statistical_exception hBirkhoff hBrehm
  refine ⟨δ, hδ, hδmax, ?_⟩
  intro η hη hηδ J hJ σ hσ hσone hσJ
  obtain ⟨Bcap, hcap, hcapone, N, _, _, _, hnull, _, hstat⟩ :=
    Hδ η hη hηδ J hJ σ hσ hσone hσJ
  refine ⟨Bcap, hcap, hcapone, ?_⟩
  intro C U hU hC hp hc hflux ρ
  have H : ∀ᵐ y ∂volume.withDensity ρ, ¬(y ∈ U ∧ C y ∈ N) := by
    rw [ae_iff]
    simp only [not_not]
    have heq : {y | y ∈ U ∧ C y ∈ N} = U ∩ C ⁻¹' N := by
      ext y; simp
    rw [heq]
    exact withDensity_absolutelyContinuous volume ρ (hnull C U hU hC hp hc hflux)
  filter_upwards [H] with y hy hyU
  exact hstat (C y) ⟨hp y hyU, hc y hyU⟩ (fun hn => hy ⟨hyU, hn⟩)

end BianchiIX
