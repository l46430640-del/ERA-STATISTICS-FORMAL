import Mathlib.MeasureTheory.Measure.Prod

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal

variable {Λ R : Type*} [MeasurableSpace Λ] [MeasurableSpace R]
variable {μ : Measure Λ} {ν : Measure R} [SFinite ν]

/-- Tonelli for a measurable set with arbitrary, possibly disconnected fibers. -/
theorem setLIntegral_fibers {A : Set (Λ × R)} {ω : Λ × R → ℝ≥0∞}
    (hA : MeasurableSet A) (hω : Measurable ω) :
    (∫⁻ p in A, ω p ∂μ.prod ν) = ∫⁻ l, ∫⁻ r in {r | (l, r) ∈ A}, ω (l, r) ∂ν ∂μ := by
  rw [← lintegral_indicator hA, lintegral_prod _ (hω.indicator hA).aemeasurable]
  apply lintegral_congr
  intro l
  have hAl : MeasurableSet {r | (l, r) ∈ A} := hA.preimage measurable_prodMk_left
  rw [← lintegral_indicator hAl]
  rfl

theorem measurable_fiber_integral {A : Set (Λ × R)} {ω : Λ × R → ℝ≥0∞}
    (hA : MeasurableSet A) (hω : Measurable ω) :
    Measurable (fun l => ∫⁻ r in {r | (l, r) ∈ A}, ω (l, r) ∂ν) := by
  have heq : (fun l => ∫⁻ r in {r | (l, r) ∈ A}, ω (l, r) ∂ν) =
      (fun l => ∫⁻ r, A.indicator ω (l, r) ∂ν) := by
    funext l
    have hAl : MeasurableSet {r | (l, r) ∈ A} := hA.preimage measurable_prodMk_left
    rw [← lintegral_indicator hAl]
    rfl
  rw [heq]
  exact (hω.indicator hA).lintegral_prod_right'

/-- Integrate the clipped fiber loss before taking any bound on the total mass. -/
theorem fiberwise_loss_integral {A F : Set (Λ × R)} {ω : Λ × R → ℝ≥0∞} {L : Λ → ℝ≥0∞}
    (hA : MeasurableSet A) (hF : MeasurableSet F) (hω : Measurable ω)
    (hbound : ∀ᵐ l ∂μ,
      (∫⁻ r in {r | (l, r) ∈ A ∩ F}, ω (l, r) ∂ν) ≤
        min (∫⁻ r in {r | (l, r) ∈ A}, ω (l, r) ∂ν) (L l)) :
    (∫⁻ p in A ∩ F, ω p ∂μ.prod ν) ≤
        ∫⁻ l, min (∫⁻ r in {r | (l, r) ∈ A}, ω (l, r) ∂ν) (L l) ∂μ ∧
      (∫⁻ l, min (∫⁻ r in {r | (l, r) ∈ A}, ω (l, r) ∂ν) (L l) ∂μ) ≤
        min (∫⁻ p in A, ω p ∂μ.prod ν) (∫⁻ l, L l ∂μ) := by
  constructor
  · rw [setLIntegral_fibers (hA.inter hF) hω]
    exact lintegral_mono_ae hbound
  · rw [setLIntegral_fibers hA hω]
    exact le_min (lintegral_mono fun _ => min_le_left _ _)
      (lintegral_mono fun _ => min_le_right _ _)

omit [SFinite ν] in
/-- Null exceptional fibers remain null after arbitrary nonnegative weighting. -/
theorem fiberwise_null_weighted {F : Set (Λ × R)} (hF : MeasurableSet F)
    (hnull : ∀ᵐ l ∂μ, ν {r | (l, r) ∈ F} = 0) (ω : Λ × R → ℝ≥0∞) :
    (∫⁻ p in F, ω p ∂μ.prod ν) = 0 := by
  have hz := Measure.measure_prod_null_of_ae_null hF hnull
  rw [Measure.restrict_eq_zero.mpr hz, lintegral_zero_measure]

end BianchiIX
