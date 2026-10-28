import BianchiIX.Algebra.StablePhaseCoefficientBounds

noncomputable section

namespace BianchiIX

theorem stableCorrectedPhase_coefficient_bounds {m u w : ℝ} (hm : 2 ≤ m) :
    let b := |u| + |w|
    |stableCorrectedGradient m u w 0 - 1| ≤ 8 / (m + 1) ^ 2 * b ^ 2 ∧
      |stableCorrectedGradient m u w 1| ≤ 6 / (m + 1) * b ∧
      |stableCorrectedGradient m u w 2| ≤ 3 / (m + 1) * b ∧
      |w ^ 2 / stableWeakRadius m w ^ 3 + stableCorrectionASecond m * u ^ 2 +
        stableCorrectionCSecond m * u * w| ≤ 33 / (m + 1) ^ 3 * b ^ 2 ∧
      |2 * stableCorrectionADeriv m * u + stableCorrectionCDeriv m * w| ≤ 12 / (m + 1) ^ 2 * b ∧
      |-(m + 1) * w / stableWeakRadius m w ^ 3 + stableCorrectionCDeriv m * u| ≤ 3 / (m + 1) ^ 2 * b := by
  let b := |u| + |w|
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hu : |u| ≤ b := le_add_of_nonneg_right (abs_nonneg w)
  have hw : |w| ≤ b := le_add_of_nonneg_left (abs_nonneg u)
  have hu2 : |u ^ 2| ≤ b ^ 2 := by simpa only [abs_pow] using pow_le_pow_left₀ (abs_nonneg u) hu 2
  have hw2 : w ^ 2 ≤ b ^ 2 := by simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg w) hw 2
  have huw : |u| * |w| ≤ b ^ 2 := by nlinarith only [mul_le_mul hu hw (abs_nonneg w) hb]
  have hL : 0 < m + 1 := by linarith
  obtain ⟨ha, ha1, ha2, hc, hc1, hc2⟩ := stableCorrection_coefficients_bounds hm
  obtain ⟨hs0, hs1, hs2, hs3, _⟩ := stableWeakRadius_coefficient_bounds (m := m) (w := w) (by linarith)
  have htri (x y z : ℝ) : |x + y + z| ≤ |x| + |y| + |z| :=
    (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have heq : stableCorrectedGradient m u w 0 - 1 =
        ((m + 1) / stableWeakRadius m w - 1) + stableCorrectionADeriv m * u ^ 2 + stableCorrectionCDeriv m * u * w := by
      dsimp [stableCorrectedGradient, stableCorrectionADeriv, stableCorrectionCDeriv]
      ring
    rw [heq]
    have H := htri ((m + 1) / stableWeakRadius m w - 1)
      (stableCorrectionADeriv m * u ^ 2) (stableCorrectionCDeriv m * u * w)
    have H0 := div_le_div_of_nonneg_right hw2 (show 0 ≤ (m + 1) ^ 2 by positivity)
    have H1 := mul_le_mul ha1 hu2 (abs_nonneg _) (by positivity : 0 ≤ 5 / (m + 1) ^ 2)
    have H2 := mul_le_mul hc1.le huw (mul_nonneg (abs_nonneg u) (abs_nonneg w)) (by positivity : 0 ≤ 2 / (m + 1) ^ 2)
    simp only [abs_mul, div_eq_mul_inv] at H H0 H1 H2 hs0 ⊢
    nlinarith only [H, H0, H1, H2, hs0]
  · have H := abs_add_le (2 * stableCorrectionA m * u) (stableCorrectionC m * w)
    have H1 := mul_le_mul ha hu (abs_nonneg u) (by positivity : 0 ≤ 2 / (m + 1))
    have H2 := mul_le_mul hc.le hw (abs_nonneg w) (by positivity : 0 ≤ 2 / (m + 1))
    dsimp [stableCorrectedGradient]
    norm_num [abs_mul] at H
    simp only [div_eq_mul_inv] at H1 H2 ⊢
    nlinarith only [H, H1, H2]
  · have H := abs_add_le (w / stableWeakRadius m w) (stableCorrectionC m * u)
    have H1 := div_le_div_of_nonneg_right hw hL.le
    have H2 := mul_le_mul hc.le hu (abs_nonneg u) (by positivity : 0 ≤ 2 / (m + 1))
    dsimp [stableCorrectedGradient]
    simp only [abs_mul, div_eq_mul_inv] at H H1 H2 hs1 ⊢
    nlinarith only [H, H1, H2, hs1]
  · have H := htri (w ^ 2 / stableWeakRadius m w ^ 3)
      (stableCorrectionASecond m * u ^ 2) (stableCorrectionCSecond m * u * w)
    have H0 := div_le_div_of_nonneg_right hw2 (show 0 ≤ (m + 1) ^ 3 by positivity)
    have H1 := mul_le_mul ha2 hu2 (abs_nonneg _) (by positivity : 0 ≤ 28 / (m + 1) ^ 3)
    have H2 := mul_le_mul hc2.le huw (mul_nonneg (abs_nonneg u) (abs_nonneg w)) (by positivity : 0 ≤ 4 / (m + 1) ^ 3)
    simp only [abs_mul, div_eq_mul_inv] at H H0 H1 H2 hs2 ⊢
    nlinarith only [H, H0, H1, H2, hs2]
  · have H := abs_add_le (2 * stableCorrectionADeriv m * u) (stableCorrectionCDeriv m * w)
    have H1 := mul_le_mul ha1 hu (abs_nonneg u) (by positivity : 0 ≤ 5 / (m + 1) ^ 2)
    have H2 := mul_le_mul hc1.le hw (abs_nonneg w) (by positivity : 0 ≤ 2 / (m + 1) ^ 2)
    norm_num [abs_mul] at H
    simp only [div_eq_mul_inv] at H1 H2 ⊢
    nlinarith only [H, H1, H2]
  · have H := abs_add_le (-(m + 1) * w / stableWeakRadius m w ^ 3) (stableCorrectionCDeriv m * u)
    have H1 := div_le_div_of_nonneg_right hw (show 0 ≤ (m + 1) ^ 2 by positivity)
    have H2 := mul_le_mul hc1.le hu (abs_nonneg u) (by positivity : 0 ≤ 2 / (m + 1) ^ 2)
    simp only [abs_mul, div_eq_mul_inv] at H H1 H2 hs3 ⊢
    nlinarith only [H, H1, H2, hs3]

end BianchiIX
