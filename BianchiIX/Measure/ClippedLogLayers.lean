import BianchiIX.Measure.PositiveLogMoments

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal

theorem integral_clipped_log_layer_one {ell B δ : ℝ} (hl : 0 < ell) (hB : 0 < B) (hδ : 0 < δ) :
    (∫ x in (0 : ℝ)..1, clippedPowerDensity ell B δ x) =
      (1 / δ) * ∫ z in (0 : ℝ)..ell, max (Real.log (B / z)) 0 := by
  rw [integral_clippedPowerDensity hl hB hδ, (integral_positive_log hl hB).2]
  ring

theorem integral_clipped_log_layer_two {ell B δ : ℝ} (hl : 0 < ell) (hB : 0 < B) (hδ : 0 < δ) :
    (∫ x in (0 : ℝ)..1, clippedPowerDensityTwo ell B δ x) =
      (1 / (2 * δ ^ 2)) * ∫ z in (0 : ℝ)..ell, (max (Real.log (B / z)) 0) ^ 2 := by
  rw [(integral_clippedPowerDensityTwo hl hB hδ).2, (integral_positive_log_sq hl hB).2]
  field_simp

/-- Equation (E.31) for one logarithmic label, on the original weighted label domain. -/
theorem lintegral_clipped_log_layer_one {ell B δ : ℝ} (hl : 0 < ell) (hB : 0 < B) (hδ : 0 < δ) :
    (∫⁻ x in Ioo (0 : ℝ) 1, ENNReal.ofReal (min ell (B * x ^ δ) / x)) =
      ENNReal.ofReal ((1 / δ) * ∫ z in (0 : ℝ)..ell, max (Real.log (B / z)) 0) := by
  rw [lintegral_clipped_log_one hl hB hδ, (integral_positive_log hl hB).2]
  congr 1
  ring

/-- Equation (E.31) for two logarithmic labels, on the original weighted label domain. -/
theorem lintegral_clipped_log_layer_two {ell B δ : ℝ} (hl : 0 < ell) (hB : 0 < B) (hδ : 0 < δ) :
    (∫⁻ x in Ioo (0 : ℝ) 1, ∫⁻ y in Ioo (0 : ℝ) 1,
      ENNReal.ofReal (min ell (B * (x * y) ^ δ) / (x * y))) =
      ENNReal.ofReal ((1 / (2 * δ ^ 2)) * ∫ z in (0 : ℝ)..ell, (max (Real.log (B / z)) 0) ^ 2) := by
  rw [lintegral_clipped_log_two hl hB hδ, (integral_positive_log_sq hl hB).2]
  congr 1
  field_simp

end BianchiIX
