import BianchiIX.Measure.FailureFlux
import BianchiIX.Measure.DyadicLogFlux

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal

def logarithmicLayerCostOne (a C σ : ℝ) : ℝ≥0∞ :=
  ∫⁻ t in Ioo (0 : ℝ) 1, ENNReal.ofReal (min a ((C * a ^ (-2 * σ)) * t ^ σ) / t)

def logarithmicFluxConstantOne (C σ : ℝ) : ℝ := (1 + Real.log C + 2 * σ) / σ

theorem logarithmicFluxConstantOne_nonneg {C σ : ℝ} (hC : 1 ≤ C) (hσ : 0 < σ) :
    0 ≤ logarithmicFluxConstantOne C σ := by
  have H := Real.log_nonneg hC
  unfold logarithmicFluxConstantOne
  positivity

theorem logarithmicLayerCostOne_le {a C σ : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (hC : 1 ≤ C) (hσ : 0 < σ) :
    logarithmicLayerCostOne a C σ ≤
      ENNReal.ofReal (logarithmicFluxConstantOne C σ * a * (1 + |Real.log a|)) := by
  have hC0 : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hB : 0 < C * a ^ (-2 * σ) := mul_pos hC0 (Real.rpow_pos_of_pos ha _)
  have hlogC := Real.log_nonneg hC
  have hloga := Real.log_nonpos ha.le ha1
  have hlogs : Real.log (C * a ^ (-2 * σ) / a) = Real.log C + (1 + 2 * σ) * |Real.log a| := by
    rw [Real.log_div hB.ne' ha.ne', Real.log_mul hC0.ne' (Real.rpow_pos_of_pos ha _).ne',
      Real.log_rpow ha, abs_of_nonpos hloga]
    ring
  unfold logarithmicLayerCostOne
  rw [lintegral_clipped_log_one ha hB hσ, hlogs, max_eq_left (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have H : 1 + (Real.log C + (1 + 2 * σ) * |Real.log a|) ≤
      (1 + Real.log C + 2 * σ) * (1 + |Real.log a|) := by
    nlinarith [mul_nonneg hlogC (abs_nonneg (Real.log a))]
  calc
    _ ≤ a / σ * (1 + (Real.log C + (1 + 2 * σ) * |Real.log a|)) :=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (min_le_left _ _) hσ.le) (by positivity)
    _ ≤ a / σ * ((1 + Real.log C + 2 * σ) * (1 + |Real.log a|)) :=
      mul_le_mul_of_nonneg_left H (div_nonneg ha.le hσ.le)
    _ = _ := by unfold logarithmicFluxConstantOne; ring

theorem dyadic_log_one_flux_sum {d C : ℝ} (hd : 0 < d) (hd1 : d ≤ 1) (hC : 0 ≤ C) :
    (∑' j, ENNReal.ofReal (C * (dyadicScale d j * (1 + |Real.log (dyadicScale d j)|)))) =
      ENNReal.ofReal (C * d * (1 + |Real.log d| + 2 * Real.log 2)) := by
  have H : HasSum (fun j => dyadicScale d j * (1 + |Real.log (dyadicScale d j)|))
      (d * (1 + |Real.log d| + 2 * Real.log 2)) := by
    convert! (hasSum_dyadic_weights.mul_left d).add (hasSum_dyadic_log_abs hd hd1) using 1
    · ext j
      dsimp only [dyadicScale]
      ring
    · ring
  rw [← ENNReal.ofReal_tsum_of_nonneg
    (fun j => mul_nonneg hC (mul_nonneg (dyadicScale_pos hd j).le (by positivity))) (H.summable.mul_left C),
    tsum_mul_left, H.tsum_eq]
  congr 1
  ring

end BianchiIX
