import BianchiIX.Statistics.EraJointStatistics
import BianchiIX.Measure.WeightedRadialPullback

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal

def eraRadialFailure (η : ℝ) (J : ℕ) (σ B Bcap a b : ℝ) (Y : ℝ → CoreAngleState) : Set ℝ :=
  Icc a b \ (fun ρ => (B, Y ρ)) ⁻¹' EraSurvivor.typicalDomain η J σ Bcap

theorem era_radial_good_iff {Γ : EraCurve} {η σ B Bcap : ℝ} {J : ℕ}
    {Y : CoreAngleState} {x : ℝ} (hx : x ∈ Ioo 0 1) (hmatch : Γ.state (2 / x) = Y) :
    x ∈ EraSurvivor.curveTypicalSet Γ η J σ B Bcap ↔ (B, Y) ∈ EraSurvivor.typicalDomain η J σ Bcap := by
  change (x ∈ Ioo 0 1 ∧ (B, Γ.state (2 / x)) ∈ EraSurvivor.typicalDomain η J σ Bcap) ↔ _
  rw [hmatch]
  exact and_iff_right hx

/-- The failure set is pulled back from the same actual-state typical set for every radial restriction. -/
theorem era_radial_failure_weighted {Γ : EraCurve} {η σ B Bcap a b c : ℝ} {J : ℕ}
    {Y : ℝ → CoreAngleState} {f : ℝ → ℝ} (hc : 0 < c)
    (hf : ∀ ρ ∈ Icc a b, DifferentiableAt ℝ f ρ) (hder : ∀ ρ ∈ Icc a b, c ≤ deriv f ρ)
    (hunit : ∀ ρ ∈ Icc a b, f ρ ∈ Ioo 0 1)
    (hmatch : ∀ ρ ∈ Icc a b, Γ.state (2 / f ρ) = Y ρ)
    (hG : MeasurableSet (EraSurvivor.curveTypicalSet Γ η J σ B Bcap))
    (hloss : volume (Ioo 0 1 \ EraSurvivor.curveTypicalSet Γ η J σ B Bcap) ≤ ENNReal.ofReal (80 * B ^ σ)) :
    MeasurableSet (eraRadialFailure η J σ B Bcap a b Y) ∧
      ∀ A : Set ℝ, MeasurableSet A → A ⊆ Icc a b → ∀ (ω : ℝ → ℝ≥0∞) (M : ℝ), 0 ≤ M →
        (∀ ρ ∈ A, ω ρ ≤ ENNReal.ofReal M) →
        (∫⁻ ρ in A ∩ eraRadialFailure η J σ B Bcap a b Y, ω ρ) ≤
          min (∫⁻ ρ in A, ω ρ) (ENNReal.ofReal (M / c) * ENNReal.ofReal (80 * B ^ σ)) := by
  let G := EraSurvivor.curveTypicalSet Γ η J σ B Bcap
  have heq : eraRadialFailure η J σ B Bcap a b Y = Icc a b \ f ⁻¹' G := by
    ext ρ
    change (ρ ∈ Icc a b ∧ (B, Y ρ) ∉ EraSurvivor.typicalDomain η J σ Bcap) ↔ (ρ ∈ Icc a b ∧ f ρ ∉ G)
    exact and_congr_right (fun hρ => not_congr (era_radial_good_iff (hunit ρ hρ) (hmatch ρ hρ)).symm)
  refine ⟨?_, ?_⟩
  · rw [heq]
    exact measurableSet_radial_failure (fun ρ hρ => (hf ρ hρ).continuousAt.continuousWithinAt)
      measurableSet_Icc Subset.rfl hG
  · intro A hA hAI ω M hM hω
    have hrestrict : A ∩ eraRadialFailure η J σ B Bcap a b Y = A \ f ⁻¹' G := by
      rw [heq]
      ext ρ
      exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hAI h.1, h.2⟩⟩
    rw [hrestrict]
    exact (radial_phase_failure_weighted hc hM hf hder hA hAI
      (fun ρ hρ => hunit ρ (hAI hρ)) hG hloss hω).2

end BianchiIX
