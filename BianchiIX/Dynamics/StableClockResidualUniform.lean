import BianchiIX.Dynamics.StableClockResidualIntegrals

noncomputable section

namespace BianchiIX

theorem exists_stableClockResidualRate_uniform_bounds :
    ∃ C > (0 : ℝ), ∀ (c s : ℝ) (y : StableState), 2 ≤ c → y ∈ stableParameterDomain c → 0 ≤ s →
      let B := C / (c + 1) ^ 2 * Real.exp (-(c + 1) / 16 * s)
      |stableClockResidualRate c s y| ≤ B ∧
        ‖fderiv ℝ (stableClockResidualRate c s) y‖ ≤ B ∧
        ‖fderiv ℝ (fderiv ℝ (stableClockResidualRate c s)) y‖ ≤ B := by
  obtain ⟨C, hC, HC⟩ := exists_stableClockResidualRate_weighted_decay
  refine ⟨4 * C, by positivity, ?_⟩
  intro c s y hc hy hs
  obtain ⟨_, h0, h1, h2⟩ := HC c s y hc hy hs
  let b := |y 1| + |y 2|
  let Q := C / (c + 1) ^ 2 * Real.exp (-(c + 1) / 16 * s)
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hb1 : b ≤ 1 := by dsimp [b]; linarith [hy.2.1, hy.2.2]
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hb2 : b ^ 2 ≤ 1 := by simpa using pow_le_pow_left₀ hb hb1 2
  have hb3 : b ^ 3 ≤ 1 := by simpa using pow_le_pow_left₀ hb hb1 3
  have heq : 4 * C / (c + 1) ^ 2 * Real.exp (-(c + 1) / 16 * s) = 4 * Q := by dsimp [Q]; ring
  dsimp only
  rw [heq]
  refine ⟨?_, ?_, ?_⟩
  · have H := mul_le_mul (show |y 1| ≤ 1 by linarith [hy.2.1]) hb3 (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    have H0 := mul_le_mul_of_nonneg_left H hQ
    dsimp only [Q, b] at H0 ⊢
    nlinarith only [h0, H0, hQ]
  · apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro v
    have H := mul_le_mul hb3 (stableFirstInputWeight_le hb1 v)
      (stableFirstInputWeight_nonneg hb v) (by norm_num : (0 : ℝ) ≤ 1)
    have H0 := mul_le_mul_of_nonneg_left H hQ
    have Hpos := mul_nonneg hQ (norm_nonneg v)
    have R := h1 v
    simp only [Real.norm_eq_abs]
    dsimp only [Q, b] at H0 Hpos ⊢
    nlinarith only [R, H0, Hpos]
  · apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro v
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro w
    have H := mul_le_mul (mul_le_mul hb2 (stableFirstInputWeight_le hb1 v)
      (stableFirstInputWeight_nonneg hb v) (by norm_num : (0 : ℝ) ≤ 1))
      (stableFirstInputWeight_le hb1 w) (stableFirstInputWeight_nonneg hb w) (by positivity)
    have H0 := mul_le_mul_of_nonneg_left H hQ
    have R := h2 v w
    simp only [Real.norm_eq_abs]
    dsimp only [Q, b] at H0 ⊢
    nlinarith only [R, H0]

end BianchiIX
