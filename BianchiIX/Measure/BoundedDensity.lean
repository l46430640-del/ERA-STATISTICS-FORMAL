import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-! Bounded densities of dominated finite measures, with their original total mass. -/

open MeasureTheory
open scoped NNReal ENNReal

namespace BianchiIX

noncomputable section

theorem rnDeriv_le_of_le_smul {X : Type*} [MeasurableSpace X]
    {μ ν : Measure X} [SigmaFinite ν] {C : ℝ≥0} (h : μ ≤ C • ν) :
    ∀ᵐ x ∂ν, μ.rnDeriv ν x ≤ C := by
  apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite (μ.measurable_rnDeriv ν)
  intro s _ _
  simpa only [lintegral_const, Measure.restrict_apply_univ, Measure.smul_apply,
    ENNReal.smul_def, smul_eq_mul] using
    (Measure.setLIntegral_rnDeriv_le s).trans (h s)

theorem exists_bounded_density_of_le_smul {X : Type*} [MeasurableSpace X]
    {μ ν : Measure X} [IsFiniteMeasure μ] [SigmaFinite ν] {C : ℝ≥0}
    (h : μ ≤ C • ν) :
    ∃ ρ : X → ℝ, Measurable ρ ∧ (∀ x, 0 ≤ ρ x) ∧
      (∀ᵐ x ∂ν, ρ x ≤ C) ∧ Integrable ρ ν ∧
      ν.withDensity (fun x => ENNReal.ofReal (ρ x)) = μ ∧
      (∫ x, ρ x ∂ν) = (μ Set.univ).toReal := by
  have hac : μ ≪ ν := by
    intro s hs
    exact le_antisymm (by simpa only [Measure.smul_apply, hs, smul_zero] using h s) bot_le
  have hb := rnDeriv_le_of_le_smul h
  refine ⟨fun x => (μ.rnDeriv ν x).toReal, (μ.measurable_rnDeriv ν).ennreal_toReal,
    fun _ => ENNReal.toReal_nonneg, ?_, ?_, ?_, ?_⟩
  · filter_upwards [hb] with x hx
    exact ENNReal.toReal_le_coe_of_le_coe hx
  · simpa only [IntegrableOn, Measure.restrict_univ] using
      (Measure.integrableOn_toReal_rnDeriv (μ := μ) (ν := ν) (measure_ne_top μ Set.univ))
  · calc
      _ = ν.withDensity (μ.rnDeriv ν) := by
        apply withDensity_congr_ae
        filter_upwards [hb] with x hx
        exact ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.coe_ne_top hx)
      _ = μ := Measure.withDensity_rnDeriv_eq μ ν hac
  · exact Measure.integral_toReal_rnDeriv hac

end
end BianchiIX
