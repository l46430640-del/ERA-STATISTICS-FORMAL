import BianchiIX.Analysis.ExitTailLength

noncomputable section

namespace BianchiIX

theorem terminal_logBand_power_ratio {α α₀ : ℝ} {J : ℕ}
    (hα : 0 < α) (hα₀ : 0 < α₀) (hJ : 1 ≤ J)
    (hband : |Real.log (α / α₀)| < Real.log 2 / J) :
    α₀ ^ J / 2 < α ^ J ∧ α ^ J < 2 * α₀ ^ J := by
  have hJ0 : 0 < (J : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hJ)
  have HM := (lt_div_iff₀ hJ0).mp hband
  rw [Real.log_div hα.ne' hα₀.ne'] at HM
  have HP := mul_le_mul_of_nonneg_right (le_abs_self (Real.log α - Real.log α₀)) hJ0.le
  have HN := mul_le_mul_of_nonneg_right (neg_abs_le (Real.log α - Real.log α₀)) hJ0.le
  constructor
  · apply (Real.log_lt_log_iff (by positivity) (pow_pos hα J)).mp
    rw [Real.log_div (pow_ne_zero J hα₀.ne') (by norm_num), Real.log_pow, Real.log_pow]
    linarith only [HM, HN]
  · apply (Real.log_lt_log_iff (pow_pos hα J) (by positivity)).mp
    rw [Real.log_mul (by norm_num) (pow_ne_zero J hα₀.ne'), Real.log_pow, Real.log_pow]
    linarith only [HM, HP]

theorem terminal_powerBand_amplitude_ratio {α α₀ : ℝ} {J : ℕ}
    (hα : 0 < α) (hα₀ : 0 < α₀) (hJ : 1 ≤ J) (hpower : α₀ ^ J ≤ 2 * α ^ J) :
    α₀ ^ (2 * J + 1) ≤ 8 * α ^ (2 * J + 1) := by
  have htwo : (2 : ℝ) ≤ 2 ^ J := by
    simpa only [pow_one] using (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hJ)
  have hp : α₀ ^ J ≤ (2 * α) ^ J := by
    rw [mul_pow]
    exact hpower.trans (mul_le_mul_of_nonneg_right htwo (pow_nonneg hα.le J))
  have hbase : α₀ ≤ 2 * α := (pow_le_pow_iff_left₀ hα₀.le (by positivity) (by omega : J ≠ 0)).mp hp
  have hsq : (α₀ ^ J) ^ 2 ≤ 4 * (α ^ J) ^ 2 := by
    have H := (sq_le_sq₀ (pow_nonneg hα₀.le J) (by positivity)).mpr hpower
    nlinarith only [H]
  have hpow (x : ℝ) : x ^ (2 * J + 1) = (x ^ J) ^ 2 * x := by
    rw [show 2 * J + 1 = J + J + 1 by omega, pow_add, pow_add, pow_one]
    ring
  calc
    α₀ ^ (2 * J + 1) = (α₀ ^ J) ^ 2 * α₀ := hpow α₀
    _ ≤ (4 * (α ^ J) ^ 2) * (2 * α) := mul_le_mul hsq hbase hα₀.le (by positivity)
    _ = 8 * α ^ (2 * J + 1) := by rw [hpow]; ring

theorem terminal_frozen_height_coefficient {η α α₀ : ℝ} {J : ℕ}
    (hη : 0 < η) (hα : 0 < α) (hα₀ : 0 < α₀) (hJ : 1 ≤ J)
    (hband : |Real.log (α / α₀)| < Real.log 2 / J) :
    η / 2 < η * α₀ ^ J / α ^ J ∧ η * α₀ ^ J / α ^ J < 2 * η := by
  have H := terminal_logBand_power_ratio hα hα₀ hJ hband
  have hp : 0 < α ^ J := pow_pos hα J
  constructor
  · apply (lt_div_iff₀ hp).mpr
    nlinarith only [mul_lt_mul_of_pos_left H.2 hη]
  · apply (div_lt_iff₀ hp).mpr
    nlinarith only [mul_lt_mul_of_pos_left H.1 hη]

end BianchiIX
