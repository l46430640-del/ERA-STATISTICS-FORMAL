import BianchiIX.Dynamics.StableClockTailIdentification

noncomputable section

namespace BianchiIX

theorem exists_stableProjectiveTail_weighted_bounds :
    ∃ C > (0 : ℝ), ∀ (c T : ℝ) (y : StableState), 2 ≤ c → y ∈ stableParameterDomain c → 0 ≤ T →
      let b := |y 1| + |y 2|
      let q := Real.exp (-(c + 1) / 16 * T)
      ContDiffAt ℝ 2 (stableProjectiveTail c T) y ∧
        |stableProjectiveTail c T y| ≤ C / (c + 1) ^ 3 * |y 1| * b ^ 3 * q ∧
        (∀ v, |fderiv ℝ (stableProjectiveTail c T) y v| ≤
          C / (c + 1) ^ 3 * b ^ 3 * stableFirstInputWeight b v * q) ∧
        (∀ v w, |fderiv ℝ (fderiv ℝ (stableProjectiveTail c T)) y v w| ≤
          C / (c + 1) ^ 3 * b ^ 2 * stableFirstInputWeight b v * stableFirstInputWeight b w * q) := by
  obtain ⟨C, hC, HC⟩ := exists_stableClockResidual_derivative_integral_tails
  refine ⟨C, hC, ?_⟩
  intro c T y hc hy hT
  dsimp only
  obtain ⟨h0, h1, h2⟩ := HC c T y hc hy hT
  refine ⟨contDiffAt_stableProjectiveTail_two hc hy hT, ?_, ?_, ?_⟩
  · rw [← stableClockTailIntegral_eq_projectiveTail hc hy hT]
    exact h0.2
  · intro v
    rw [stableProjectiveTail_fderiv_clockIntegral hc hy hT]
    exact (h1 v).2
  · intro v w
    rw [stableProjectiveTail_fderiv2_clockIntegral hc hy hT]
    exact (h2 v w).2

end BianchiIX
