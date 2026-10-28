import BianchiIX.Statistics.CommonCoreRestart
import BianchiIX.Statistics.EraSurvivorMeasurability

noncomputable section

namespace BianchiIX

open Set MeasureTheory

/-- The selected physical core and all its finite-history states, digits, code, and phases use the same measurable return cap. -/
theorem exists_common_borel_era_coding
    (hBirkhoff : Literature.BirkhoffErgodicInput ℝ)
    (hBrehm : Literature.BrehmIXAttractorInput) :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 20 ≤ J → ∀ σ : ℝ, 0 < σ → σ < 1 → σ * (2 * J : ℕ) < 1 →
        ∀ Bbound : ℝ, 0 < Bbound → ∃ Bcap > (0 : ℝ), Bcap < 1 ∧ Bcap ≤ Bbound ∧
          (∀ m : ℕ, MeasurableSet (eraSelectedInputs η J σ Bcap m) ∧
            Measurable (fun p : eraSelectedInputs η J σ Bcap m => eraBudgetReturn η J m p.val)) ∧
          ∃ N : Set NormalizedState, MeasurableSet N ∧ N ⊆ physicalPhaseSpace ∧
            geometricException ⊆ N ∧
            (∀ x : NormalizedState, ∀ t ∈ normalizedMaxDomain x 0,
              normalizedMaxCurve x 0 t ∈ N ↔ x ∈ N) ∧
            (∀ (C : SectionCoordinates → NormalizedState) (U : Set SectionCoordinates),
              IsOpen U → (∀ y ∈ U, ContDiffAt ℝ 1 C y) →
              (∀ y ∈ U, positiveWalls (C y)) → (∀ y ∈ U, stateConstraint (C y) = 1) →
              (∀ y ∈ U, normalizedSectionFlux (C y) (fun i => fderiv ℝ C y (Pi.single i 1)) ≠ 0) →
              volume (U ∩ C ⁻¹' N) = 0) ∧ NullInFourCoordinates N ∧
            ∃ W : NormalizedState → CoreRestartData, Measurable W ∧
              (∀ x ∈ physicalPhaseSpace, x ∉ N → CoreRestartWitness η J σ Bcap x (W x)) ∧
              ∃ p : ↥(physicalPhaseSpace \ N) → eraSurvivorDomain η J σ Bcap,
                Measurable p ∧ Measurable (EraSurvivor.digits ∘ p) ∧
                Measurable (EraSurvivor.code ∘ p) ∧ Measurable (EraSurvivor.state ∘ p) ∧
                Measurable (EraSurvivor.phase ∘ p) ∧
                ∀ x, (p x).val = (W x.val).2 ∧
                  EraStatistics (EraSurvivor.digits (p x)) (EraSurvivor.phase (p x)) := by
  obtain ⟨δG, hδG, hδmax, HG⟩ := exists_common_borel_core_restart hBirkhoff hBrehm
  obtain ⟨δM, hδM, _, HM⟩ := exists_era_selected_inputs_measurable
  refine ⟨min δG δM, lt_min hδG hδM, (min_le_left _ _).trans hδmax, ?_⟩
  intro η hη hηδ J hJ σ hσ hσone hσJ Bbound hBbound
  obtain ⟨_, _, _, HB⟩ := HG η hη (hηδ.trans (min_le_left _ _)) J hJ σ hσ hσone hσJ
  obtain ⟨BM, hBM, hBMone, Hinputs⟩ :=
    HM η hη (hηδ.trans (min_le_right _ _)) J hJ σ hσ hσone hσJ
  let Bcap := min BM Bbound
  have hcap : 0 < Bcap := lt_min hBM hBbound
  have hcapone : Bcap < 1 := (min_le_left _ _).trans_lt hBMone
  have Hmeas (m : ℕ) := eraSelectedInputs_measurable_of_contDiff (η := η) (J := J) (Bstar := Bcap) hσ.le
    (fun p hp => (Hinputs m).1 p ⟨⟨hp.1.1, hp.1.2.trans (min_le_left _ _)⟩, hp.2⟩)
  obtain ⟨N, hNm, hNp, hNg, hNi, hNn, hNfour, W, hW, HWB⟩ := HB Bcap hcap
  have HW (x : NormalizedState) (hx : x ∈ physicalPhaseSpace) (hn : x ∉ N) :
      CoreRestartWitness η J σ Bcap x (W x) := by
    obtain ⟨hB, H⟩ := HWB x hx hn
    exact H.restrict_cap (hB.trans hcapone.le) hB
  obtain ⟨p, hpm, Hp⟩ := CoreRestartWitness.exists_measurable_survivor
    (S := physicalPhaseSpace \ N) (C := id) hW (fun x hx => HW x hx.1 hx.2)
  exact ⟨Bcap, hcap, hcapone, min_le_right _ _, Hmeas, N, hNm, hNp, hNg, hNi, hNn, hNfour,
    W, hW, HW, p, hpm, (EraSurvivor.digits_measurable Hmeas).comp hpm,
    (EraSurvivor.code_measurable Hmeas).comp hpm, (EraSurvivor.state_measurable Hmeas).comp hpm,
    (EraSurvivor.phase_measurable Hmeas).comp hpm, Hp⟩

end BianchiIX
