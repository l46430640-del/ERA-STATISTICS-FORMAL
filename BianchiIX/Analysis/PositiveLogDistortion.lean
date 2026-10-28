import BianchiIX.Analysis.InverseLogDistortion

noncomputable section

namespace BianchiIX

/-- A positive derivative bounded below by one half has logarithmic error at most twice its additive error. -/
theorem abs_log_le_twice_sub_one_of_half_le {t : ℝ} (ht : 1 / 2 ≤ t) :
    |Real.log t| ≤ 2 * |t - 1| := by
  have ht0 : 0 < t := by linarith only [ht]
  have ha := abs_nonneg (t - 1)
  have hlo := neg_le_abs (t - 1)
  have hhi := le_abs_self (t - 1)
  have hinv : 1 / t ≤ 1 + 2 * |t - 1| := (div_le_iff₀ ht0).mpr (by
    nlinarith only [hlo, mul_le_mul_of_nonneg_right ht ha])
  have Hlo := Real.one_sub_inv_le_log_of_pos ht0
  have Hhi := Real.log_le_sub_one_of_pos ht0
  rw [inv_eq_one_div] at Hlo
  exact abs_le.mpr ⟨by linarith only [Hlo, hinv], by linarith only [Hhi, hhi, ha]⟩

end BianchiIX
