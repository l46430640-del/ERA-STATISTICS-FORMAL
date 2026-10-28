import BianchiIX.Measure.OneLogFlux
import BianchiIX.Statistics.RestartEraStatistics

noncomputable section

namespace BianchiIX

def angularFailureFluxConstant (L σ : ℝ) : ℝ := 640 * Real.sqrt 3 * (102400 * (L + 1)) ^ σ

theorem angularFailureFluxConstant_ge_one {L σ : ℝ} (hL : 0 ≤ L) (hσ : 0 ≤ σ) :
    1 ≤ angularFailureFluxConstant L σ := by
  have hp : 1 ≤ (102400 * (L + 1)) ^ σ := Real.one_le_rpow (by linarith) hσ
  have hs : 1 ≤ Real.sqrt (3 : ℝ) := Real.one_le_sqrt.mpr (by norm_num)
  have H := mul_le_mul hs hp (by norm_num : (0 : ℝ) ≤ 1) (Real.sqrt_nonneg _)
  dsimp only [angularFailureFluxConstant]
  nlinarith only [H]

theorem restartAmplitudeBudget_normalized {L a t σ : ℝ} (hL : 0 ≤ L) (ha : 0 < a) (ht : 0 ≤ t) :
    640 * Real.sqrt 3 * (restartAmplitudeBudget L a (2 * a * t)) ^ σ =
      (angularFailureFluxConstant L σ * a ^ (-2 * σ)) * t ^ σ := by
  have hB : restartAmplitudeBudget L a (2 * a * t) = (102400 * (L + 1)) * (a ^ (-2 : ℝ) * t) := by
    rw [Real.rpow_neg ha.le, Real.rpow_two]
    unfold restartAmplitudeBudget
    field_simp
    ring
  rw [hB, Real.mul_rpow (by positivity) (mul_nonneg (Real.rpow_nonneg ha.le _) ht),
    Real.mul_rpow (Real.rpow_nonneg ha.le _) ht, ← Real.rpow_mul ha.le]
  dsimp only [angularFailureFluxConstant]
  ring

end BianchiIX
