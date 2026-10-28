import BianchiIX.Algebra.StablePhaseHessian

noncomputable section

namespace BianchiIX

theorem stableCorrectionA_partial_fractions {m : ℝ} (hm : 1 < m) :
    stableCorrectionA m = (1 / (m - 1) + 1 / (m + 1)) / 2 ∧
      stableCorrectionADeriv m = -(1 / (m - 1) ^ 2 + 1 / (m + 1) ^ 2) / 2 ∧
      stableCorrectionASecond m = 1 / (m - 1) ^ 3 + 1 / (m + 1) ^ 3 := by
  have h1 : m - 1 ≠ 0 := by linarith
  have h2 : m + 1 ≠ 0 := by linarith
  have h3 : m ^ 2 - 1 ≠ 0 := by nlinarith
  dsimp [stableCorrectionA, stableCorrectionADeriv, stableCorrectionASecond]
  refine ⟨?_, ?_, ?_⟩ <;> field_simp <;> ring

theorem stableCorrection_coefficients_bounds {m : ℝ} (hm : 2 ≤ m) :
    |stableCorrectionA m| ≤ 2 / (m + 1) ∧
      |stableCorrectionADeriv m| ≤ 5 / (m + 1) ^ 2 ∧
      |stableCorrectionASecond m| ≤ 28 / (m + 1) ^ 3 ∧
      |stableCorrectionC m| = 2 / (m + 1) ∧
      |stableCorrectionCDeriv m| = 2 / (m + 1) ^ 2 ∧
      |stableCorrectionCSecond m| = 4 / (m + 1) ^ 3 := by
  have hL : 0 < m + 1 := by linarith
  have hD : 0 < m - 1 := by linarith
  have hp (n : ℕ) : 1 / (m - 1) ^ n ≤ 3 ^ n / (m + 1) ^ n := by
    apply (div_le_div_iff₀ (pow_pos hD n) (pow_pos hL n)).mpr
    simpa only [one_mul, mul_pow] using
      pow_le_pow_left₀ hL.le (show m + 1 ≤ 3 * (m - 1) by linarith) n
  obtain ⟨h0, h1, h2⟩ := stableCorrectionA_partial_fractions (by linarith : 1 < m)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h0, abs_of_nonneg (by positivity)]
    have H := hp 1
    norm_num only [pow_one] at H
    simp only [div_eq_mul_inv, one_mul] at H ⊢
    linarith only [H]
  · rw [h1, neg_div, abs_neg, abs_of_nonneg (by positivity)]
    have H := hp 2
    norm_num only [Nat.reducePow] at H
    simp only [div_eq_mul_inv, one_mul] at H ⊢
    linarith only [H]
  · rw [h2, abs_of_nonneg (by positivity)]
    have H := hp 3
    norm_num only [Nat.reducePow] at H
    simp only [div_eq_mul_inv, one_mul] at H ⊢
    linarith only [H]
  · simp [stableCorrectionC, abs_div, abs_of_pos hL]
  · rw [stableCorrectionCDeriv, abs_of_nonneg (by positivity)]
  · simp [stableCorrectionCSecond, abs_div, abs_of_pos hL]

theorem stableWeakRadius_coefficient_bounds {m w : ℝ} (hm : -1 < m) :
    |(m + 1) / stableWeakRadius m w - 1| ≤ w ^ 2 / (m + 1) ^ 2 ∧
      |w / stableWeakRadius m w| ≤ |w| / (m + 1) ∧
      |w ^ 2 / stableWeakRadius m w ^ 3| ≤ w ^ 2 / (m + 1) ^ 3 ∧
      |-(m + 1) * w / stableWeakRadius m w ^ 3| ≤ |w| / (m + 1) ^ 2 ∧
      |(m + 1) ^ 2 / stableWeakRadius m w ^ 3| ≤ 1 / (m + 1) := by
  have hL : 0 < m + 1 := by linarith
  have hS := stableWeakRadius_pos (w := w) hm
  have hLS : m + 1 ≤ stableWeakRadius m w := phaseNorm_ge hL.le
  have h3 := pow_le_pow_left₀ hL.le hLS 3
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have H := phaseNorm_ratio_defect (b := w) hL
    change 1 - (m + 1) / stableWeakRadius m w =
      w ^ 2 * (1 / (stableWeakRadius m w * (stableWeakRadius m w + (m + 1)))) at H
    rw [abs_sub_comm, H, abs_of_nonneg (by positivity), mul_one_div]
    apply div_le_div_of_nonneg_left (sq_nonneg w) (pow_pos hL 2)
    have H0 := mul_le_mul hLS (show m + 1 ≤ stableWeakRadius m w + (m + 1) by linarith)
      hL.le hS.le
    nlinarith only [H0]
  · rw [abs_div, abs_of_pos hS]
    exact div_le_div_of_nonneg_left (abs_nonneg w) hL hLS
  · rw [abs_of_nonneg (by positivity)]
    exact div_le_div_of_nonneg_left (sq_nonneg w) (pow_pos hL 3) h3
  · rw [abs_div, abs_mul, abs_neg, abs_of_pos hL, abs_of_pos (pow_pos hS 3)]
    calc
      _ ≤ (m + 1) * |w| / (m + 1) ^ 3 :=
        div_le_div_of_nonneg_left (by positivity) (pow_pos hL 3) h3
      _ = |w| / (m + 1) ^ 2 := by field_simp
  · rw [abs_of_nonneg (by positivity)]
    calc
      _ ≤ (m + 1) ^ 2 / (m + 1) ^ 3 :=
        div_le_div_of_nonneg_left (sq_nonneg _) (pow_pos hL 3) h3
      _ = 1 / (m + 1) := by field_simp

end BianchiIX
