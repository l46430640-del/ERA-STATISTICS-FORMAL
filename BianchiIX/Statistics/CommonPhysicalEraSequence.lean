import BianchiIX.Statistics.CommonEraOrbit
import BianchiIX.Statistics.PhysicalEraSequence

noncomputable section

namespace BianchiIX

open Set MeasureTheory

/-- Jointly Borel complete physical eras outside one invariant null set, with the full statistical law. -/
theorem exists_common_physical_era_sequence
    (hBirkhoff : Literature.BirkhoffErgodicInput ℝ)
    (hBrehm : Literature.BrehmIXAttractorInput) :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 20 ≤ J → ∀ σ : ℝ, 0 < σ → σ < 1 → σ * (2 * J : ℕ) < 1 →
        ∃ N : Set NormalizedState, MeasurableSet N ∧ N ⊆ physicalPhaseSpace ∧
          geometricException ⊆ N ∧
          (∀ x : NormalizedState, ∀ s ∈ normalizedMaxDomain x 0,
            normalizedMaxCurve x 0 s ∈ N ↔ x ∈ N) ∧
          (∀ (C : SectionCoordinates → NormalizedState) (U : Set SectionCoordinates),
            IsOpen U → (∀ y ∈ U, ContDiffAt ℝ 1 C y) →
            (∀ y ∈ U, positiveWalls (C y)) → (∀ y ∈ U, stateConstraint (C y) = 1) →
            (∀ y ∈ U, normalizedSectionFlux (C y) (fun i => fderiv ℝ C y (Pi.single i 1)) ≠ 0) →
            volume (U ∩ C ⁻¹' N) = 0) ∧ NullInFourCoordinates N ∧
          ∃ K : ↥(physicalPhaseSpace \ N) → ℕ → ℕ+, Measurable K ∧
          ∃ Y : ↥(physicalPhaseSpace \ N) → ℕ → CoreAngleState, Measurable Y ∧
          ∃ t : ↥(physicalPhaseSpace \ N) → ℕ → ℝ, Measurable t ∧
          ∃ a : ↥(physicalPhaseSpace \ N) → ℕ → Fin 6, Measurable a ∧
            ∀ x, PhysicalEraSequence η J x.val (K x) (Y x) (t x) (a x) := by
  obtain ⟨δ, hδ, hδmax, H⟩ := exists_common_borel_era_orbit hBirkhoff hBrehm
  refine ⟨δ, hδ, hδmax, ?_⟩
  intro η hη hηδ J hJ σ hσ hσone hσJ
  obtain ⟨Bcap, _, _, N, hNm, hNp, hNg, hNi, hNn, hNfour,
    W, _, p, _, had, _, has, _, hat, haf, Hp⟩ := H η hη hηδ J hJ σ hσ hσone hσJ
  refine ⟨N, hNm, hNp, hNg, hNi, hNn, hNfour,
    (fun x n => EraSurvivor.digits (p x) (n + 1)), ?_,
    (fun x n => EraSurvivor.state (p x) (n + 1)), ?_,
    (fun x n => EraSurvivor.physicalTime (W x.val) (p x) (n + 1)), ?_,
    (fun x n => EraSurvivor.physicalFrame (W x.val) (p x) (n + 1)), ?_, ?_⟩
  · exact measurable_pi_lambda _ (fun n => (measurable_pi_apply (n + 1)).comp had)
  · exact measurable_pi_lambda _ (fun n => (measurable_pi_apply (n + 1)).comp has)
  · exact measurable_pi_lambda _ (fun n => (measurable_pi_apply (n + 1)).comp hat)
  · exact measurable_pi_lambda _ (fun n => (measurable_pi_apply (n + 1)).comp haf)
  · intro x
    obtain ⟨_, Hstat, _, _, Hmono, Htop, Hn⟩ := Hp x
    exact EraSurvivor.physical_era_sequence (W x.val) (p x) x.property.1.2 Hstat
      (fun n => ⟨(Hn n).1, (Hn n).2.1⟩) Hmono Htop
      (fun n => ⟨(Hn n).2.2.1, (Hn n).2.2.2.2⟩)

end BianchiIX
