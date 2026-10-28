import BianchiIX.Dynamics.StableCorrectedTailIdentification

noncomputable section

namespace BianchiIX

theorem exists_stableCorrectedPhaseTail_weighted_bounds :
    ∃ C > (0 : ℝ), ∀ (c T : ℝ) (y : StableState), 2 ≤ c → y ∈ stableParameterDomain c → 0 ≤ T →
      let b := |y 1| + |y 2|
      let q := Real.exp (-(c + 1) / 16 * T)
      ContDiffAt ℝ 2 (stableCorrectedPhaseTail (c + 1) T) y ∧
        |stableCorrectedPhaseTail (c + 1) T y| ≤ C / (c + 1) ^ 3 * |y 1| * b ^ 3 * q ∧
        (∀ v, |fderiv ℝ (stableCorrectedPhaseTail (c + 1) T) y v| ≤
          C / (c + 1) ^ 3 * b ^ 3 * stableFirstInputWeight b v * q) ∧
        (∀ v w, |fderiv ℝ (fderiv ℝ (stableCorrectedPhaseTail (c + 1) T)) y v w| ≤
          C / (c + 1) ^ 3 * b ^ 2 * stableFirstInputWeight b v * stableFirstInputWeight b w * q) := by
  obtain ⟨C, hC, HC⟩ := exists_stableResidual_derivative_integral_tails
  refine ⟨C, hC, ?_⟩
  intro c T y hc hy hT
  dsimp only
  obtain ⟨h0, h1, h2⟩ := HC c T y hc hy.1 hy.2.1 hy.2.2 hT
  refine ⟨contDiffAt_stableCorrectedPhaseTail_two hc hy hT, ?_, ?_, ?_⟩
  · rw [← stableResidualTailIntegral_eq_correctedPhaseTail hc hy hT]
    exact h0.2
  · intro v
    rw [stableCorrectedPhaseTail_fderiv_apply hc hy hT]
    exact (h1 v).2
  · intro v w
    rw [stableCorrectedPhaseTail_fderiv2_apply hc hy hT]
    exact (h2 v w).2

theorem exists_stableCorrectedRemainder_weighted_bounds :
    ∃ C > (0 : ℝ), ∀ y : StableState, 2 ≤ y 0 → |y 1| < 1 / 200 → |y 2| < 1 / 200 →
      let b := |y 1| + |y 2|
      ContDiffAt ℝ 2 stableCorrectedRemainder y ∧
        |stableCorrectedRemainder y| ≤ C / (y 0 + 1) ^ 3 * |y 1| * b ^ 3 ∧
        (∀ v, |fderiv ℝ stableCorrectedRemainder y v| ≤
          C / (y 0 + 1) ^ 3 * b ^ 3 * stableFirstInputWeight b v) ∧
        (∀ v w, |fderiv ℝ (fderiv ℝ stableCorrectedRemainder) y v w| ≤
          C / (y 0 + 1) ^ 3 * b ^ 2 * stableFirstInputWeight b v * stableFirstInputWeight b w) := by
  obtain ⟨C, hC, HC⟩ := exists_stableCorrectedPhaseTail_weighted_bounds
  refine ⟨C, hC, ?_⟩
  intro y hm hu hw
  have H := HC (y 0) 0 y hm ⟨by simp, hu, hw⟩ (le_refl 0)
  simpa only [stableCorrectedPhaseTail_zero, mul_zero, Real.exp_zero, mul_one] using H

theorem exists_stableCorrectedRemainder_amplitude_bounds :
    ∃ C > (0 : ℝ), ∀ y : StableState, 2 ≤ y 0 → |y 1| < 1 / 200 → |y 2| < 1 / 200 →
      let b := |y 1| + |y 2|
      let Q := C / (y 0 + 1) ^ 3
      (∀ v, |fderiv ℝ stableCorrectedRemainder y v| ≤ Q * b ^ 3 * ‖v‖) ∧
      (∀ v, v 1 = 0 → v 2 = 0 → |fderiv ℝ stableCorrectedRemainder y v| ≤ Q * b ^ 4 * ‖v‖) ∧
      (∀ v w, |fderiv ℝ (fderiv ℝ stableCorrectedRemainder) y v w| ≤ Q * b ^ 2 * ‖v‖ * ‖w‖) ∧
      (∀ v w, v 1 = 0 → v 2 = 0 →
        |fderiv ℝ (fderiv ℝ stableCorrectedRemainder) y v w| ≤ Q * b ^ 3 * ‖v‖ * ‖w‖) ∧
      (∀ v w, v 1 = 0 → v 2 = 0 → w 1 = 0 → w 2 = 0 →
        |fderiv ℝ (fderiv ℝ stableCorrectedRemainder) y v w| ≤ Q * b ^ 4 * ‖v‖ * ‖w‖) := by
  obtain ⟨C, hC, HC⟩ := exists_stableCorrectedRemainder_weighted_bounds
  refine ⟨4 * C, by positivity, ?_⟩
  intro y hm hu hw
  obtain ⟨_, _, h1, h2⟩ := HC y hm hu hw
  let b := |y 1| + |y 2|
  let Q := C / (y 0 + 1) ^ 3
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hb1 : b ≤ 1 := by dsimp [b]; linarith
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hscale : 4 * C / (y 0 + 1) ^ 3 = 4 * Q := by dsimp [Q]; ring
  dsimp only
  rw [hscale]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro v
    have R := h1 v
    have H := mul_le_mul_of_nonneg_left (stableFirstInputWeight_le hb1 v) (show 0 ≤ Q * b ^ 3 by positivity)
    have hpos : 0 ≤ Q * b ^ 3 * ‖v‖ := by positivity
    dsimp only [Q, b] at H hpos ⊢
    nlinarith only [R, H, hpos]
  · intro v hv1 hv2
    have R := h1 v
    rw [stableFirstInputWeight_center _ hv1 hv2] at R
    have hpos : 0 ≤ Q * b ^ 4 * ‖v‖ := by positivity
    dsimp only [Q, b] at hpos ⊢
    nlinarith only [R, hpos]
  · intro v w
    have R := h2 v w
    have H := mul_le_mul_of_nonneg_left
      (mul_le_mul (stableFirstInputWeight_le hb1 v) (stableFirstInputWeight_le hb1 w)
        (stableFirstInputWeight_nonneg hb w) (by positivity)) (show 0 ≤ Q * b ^ 2 by positivity)
    dsimp only [Q, b] at H ⊢
    nlinarith only [R, H]
  · intro v w hv1 hv2
    have R := h2 v w
    rw [stableFirstInputWeight_center _ hv1 hv2] at R
    have H := mul_le_mul_of_nonneg_left (stableFirstInputWeight_le hb1 w)
      (show 0 ≤ Q * b ^ 2 * (b * ‖v‖) by positivity)
    have hpos : 0 ≤ Q * b ^ 3 * ‖v‖ * ‖w‖ := by positivity
    dsimp only [Q, b] at H hpos ⊢
    nlinarith only [R, H, hpos]
  · intro v w hv1 hv2 hw1 hw2
    have R := h2 v w
    rw [stableFirstInputWeight_center _ hv1 hv2, stableFirstInputWeight_center _ hw1 hw2] at R
    have hpos : 0 ≤ Q * b ^ 4 * ‖v‖ * ‖w‖ := by positivity
    dsimp only [Q, b] at hpos ⊢
    nlinarith only [R, hpos]

end BianchiIX
