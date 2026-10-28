import BianchiIX.Dynamics.StableProjectiveTailWeighted

noncomputable section

namespace BianchiIX

/-- Ordinary initial-state derivatives, with the clock scale and cutoff held fixed. -/
theorem exists_stableProjectiveTail_amplitude_bounds :
    ∃ C > (0 : ℝ), ∀ (c T : ℝ) (y : StableState), 2 ≤ c → y ∈ stableParameterDomain c → 0 ≤ T →
      let b := |y 1| + |y 2|
      let Q := C / (c + 1) ^ 3 * Real.exp (-(c + 1) / 16 * T)
      |stableProjectiveTail c T y| ≤ Q * b ^ 4 ∧
      (∀ v, |fderiv ℝ (stableProjectiveTail c T) y v| ≤ Q * b ^ 3 * ‖v‖) ∧
      (∀ v, v 1 = 0 → v 2 = 0 → |fderiv ℝ (stableProjectiveTail c T) y v| ≤ Q * b ^ 4 * ‖v‖) ∧
      (∀ v w, |fderiv ℝ (fderiv ℝ (stableProjectiveTail c T)) y v w| ≤ Q * b ^ 2 * ‖v‖ * ‖w‖) ∧
      (∀ v w, v 1 = 0 → v 2 = 0 →
        |fderiv ℝ (fderiv ℝ (stableProjectiveTail c T)) y v w| ≤ Q * b ^ 3 * ‖v‖ * ‖w‖) ∧
      (∀ v w, v 1 = 0 → v 2 = 0 → w 1 = 0 → w 2 = 0 →
        |fderiv ℝ (fderiv ℝ (stableProjectiveTail c T)) y v w| ≤ Q * b ^ 4 * ‖v‖ * ‖w‖) := by
  obtain ⟨C, hC, HC⟩ := exists_stableProjectiveTail_weighted_bounds
  refine ⟨4 * C, by positivity, ?_⟩
  intro c T y hc hy hT
  obtain ⟨_, h0, h1, h2⟩ := HC c T y hc hy hT
  let b := |y 1| + |y 2|
  let Q := C / (c + 1) ^ 3 * Real.exp (-(c + 1) / 16 * T)
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hb1 : b ≤ 1 := by dsimp [b]; linarith [hy.2.1, hy.2.2]
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hscale : 4 * C / (c + 1) ^ 3 * Real.exp (-(c + 1) / 16 * T) = 4 * Q := by dsimp [Q]; ring
  dsimp only
  rw [hscale]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have H := mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_right (abs_nonneg (y 2)) : |y 1| ≤ b)
      (show 0 ≤ Q * b ^ 3 by positivity)
    have hpos : 0 ≤ Q * b ^ 4 := by positivity
    dsimp only [Q, b] at H hpos ⊢
    nlinarith only [h0, H, hpos]
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
