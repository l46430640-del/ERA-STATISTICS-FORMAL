import BianchiIX.Statistics.EraBoundedDigits
import BianchiIX.Measure.ThreeCoordinateTonelli

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal

/-- The positive-wall core coordinates with a bounded actual survivor code. -/
def coreBoundedDigits (η : ℝ) (J : ℕ) (σ B Bcap : ℝ) : Set CoreAngleState :=
  {q | q 0 ∈ Ioo (0 : ℝ) 1 ∧ 0 < q 1 ∧ 0 < q 2 ∧ q 1 + q 2 ≤ B ∧
    (B, ![2 / q 0, q 1, q 2]) ∈ EraSurvivor.boundedDigitDomain η J σ Bcap}

theorem measurableSet_coreBoundedDigits {η σ B Bcap : ℝ} {J : ℕ}
    (H : MeasurableSet (EraSurvivor.boundedDigitDomain η J σ Bcap)) :
    MeasurableSet (coreBoundedDigits η J σ B Bcap) := by
  have hs : Measurable (fun q : CoreAngleState => q 1 + q 2) := by fun_prop
  have hp : Measurable (fun q : CoreAngleState => (B, ![2 / q 0, q 1, q 2])) := by fun_prop
  exact (measurableSet_Ioo.preimage (measurable_pi_apply 0)).inter
    ((measurableSet_lt measurable_const (measurable_pi_apply 1)).inter
      ((measurableSet_lt measurable_const (measurable_pi_apply 2)).inter
        ((measurableSet_le hs measurable_const).inter (H.preimage hp))))

/-- Tonelli transfers zero measure on constant-amplitude curves to three-dimensional core coordinates. -/
theorem volume_coreBoundedDigits_zero {η σ B Bcap : ℝ} {J : ℕ}
    (hjoint : MeasurableSet (EraSurvivor.boundedDigitDomain η J σ Bcap))
    (H : ∀ Γ : EraCurve, Γ.Admissible B →
      volume (EraSurvivor.curveBoundedDigits Γ η J σ B Bcap) = 0) :
    volume (coreBoundedDigits η J σ B Bcap) = 0 := by
  let A := coreBoundedDigits η J σ B Bcap
  have hA : MeasurableSet A := measurableSet_coreBoundedDigits hjoint
  have hslices (u w : ℝ) : volume ((fun x : ℝ => ![x, u, w]) ⁻¹' A) = 0 := by
    by_cases hl : 0 < u ∧ 0 < w ∧ u + w ≤ B
    · let Γ : EraCurve := ⟨fun _ => u, fun _ => w⟩
      have hΓ : Γ.Admissible B := by
        intro r _
        refine ⟨hl.1, hl.2.1, hl.2.2, contDiffAt_const, contDiffAt_const, ?_, ?_⟩ <;>
          simpa only [Γ, deriv_const, abs_zero] using Real.sqrt_nonneg _
      have heq : (fun x : ℝ => ![x, u, w]) ⁻¹' A =
          EraSurvivor.curveBoundedDigits Γ η J σ B Bcap := by
        ext x
        simp [A, coreBoundedDigits, EraSurvivor.curveBoundedDigits, EraCurve.state, Γ, hl.1, hl.2.1, hl.2.2]
      rw [heq]
      exact H Γ hΓ
    · have heq : (fun x : ℝ => ![x, u, w]) ⁻¹' A = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro x hx
        exact hl ⟨hx.2.1, hx.2.2.1, hx.2.2.2.1⟩
      rw [heq, measure_empty]
  change volume A = 0
  have hind : Measurable (A.indicator (1 : CoreAngleState → ℝ≥0∞)) := measurable_const.indicator hA
  rw [← lintegral_indicator_one hA, lintegral_three_coordinates hind]
  have hinner (u w : ℝ) : (∫⁻ x : ℝ, A.indicator (1 : CoreAngleState → ℝ≥0∞) ![x, u, w]) = 0 := by
    have heq : (fun x : ℝ => A.indicator (1 : CoreAngleState → ℝ≥0∞) ![x, u, w]) =
        ((fun x : ℝ => ![x, u, w]) ⁻¹' A).indicator 1 := by
      funext x
      rfl
    rw [heq, lintegral_indicator_one (hA.preimage (by fun_prop)), hslices]
  simp_rw [hinner]
  simp

theorem exists_core_boundedDigits_zero (hBirkhoff : Literature.BirkhoffErgodicInput ℝ) :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 20 ≤ J → ∀ σ : ℝ, 0 < σ → σ < 1 → σ * (2 * J : ℕ) < 1 →
        ∃ Bcap > (0 : ℝ), Bcap < 1 ∧ ∃ Bstar > (0 : ℝ), Bstar ≤ Bcap ∧
          ∀ B ∈ Ioc 0 Bstar, MeasurableSet (coreBoundedDigits η J σ B Bcap) ∧
            volume (coreBoundedDigits η J σ B Bcap) = 0 := by
  obtain ⟨δ, hδ, hδmax, Hδ⟩ := exists_era_curve_boundedDigits_zero hBirkhoff
  refine ⟨δ, hδ, hδmax, ?_⟩
  intro η hη hηδ J hJ σ hσ hσone hσJ
  obtain ⟨Bcap, hcap, hcapone, hjoint, Bstar, hBstar, hBcap, H⟩ := Hδ η hη hηδ J hJ σ hσ hσone hσJ
  exact ⟨Bcap, hcap, hcapone, Bstar, hBstar, hBcap, fun B hB =>
    ⟨measurableSet_coreBoundedDigits hjoint, volume_coreBoundedDigits_zero hjoint (H B hB)⟩⟩

end BianchiIX
