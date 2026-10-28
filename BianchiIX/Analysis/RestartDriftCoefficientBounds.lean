import BianchiIX.Analysis.VanishingAxis
import BianchiIX.Dynamics.RestartDriftCoefficients

noncomputable section

namespace BianchiIX

/-- The two exact vanishings replace separate estimates of every root and rotation term. -/
theorem exists_restartRadialDriftCoefficients_bounds :
    ∃ C ≥ (1 : ℝ), ∀ (n : ℝ) (Z : RestartCenterState), |n| ≤ 1 / 16 → ‖Z‖ ≤ 1 / 16 →
      ‖restartRadialDriftCoefficients (n, Z)‖ ≤ C * (|n| + ‖Z‖) * ‖Z‖ ∧
      ‖fderiv ℝ restartRadialDriftCoefficients (n, Z)‖ ≤ C * (|n| + ‖Z‖) ∧
      ‖fderiv ℝ restartRadialDriftCoefficients (n, Z) (1, 0)‖ ≤ C * ‖Z‖ := by
  have hreg (p : RestartRadialState) (hp : ‖p‖ ≤ 1 / 16) :
      ContDiffAt ℝ 3 restartRadialDriftCoefficients p := by
    have hn : |p.1| ≤ 1 / 16 := (norm_fst_le p).trans hp
    have hZ := (norm_snd_le p).trans hp
    exact contDiffAt_restartRadialDriftCoefficients
      (by obtain ⟨hl, hu⟩ := abs_le.mp hn; nlinarith only [hl, hu])
      (restartSectionRadicand_pos_of_small hn hZ)
  obtain ⟨C, hC, HC⟩ := exists_bounds_of_vanishing_axis (by norm_num : (0 : ℝ) ≤ 1 / 16)
    hreg restartRadialDriftCoefficients_axis restartRadialDriftCoefficients_fderiv_zero
  refine ⟨C, hC, ?_⟩
  intro n Z hn hZ
  have H := HC (n, Z) (by simpa only [Prod.norm_def, Real.norm_eq_abs, max_le_iff] using ⟨hn, hZ⟩)
  have hC0 : 0 ≤ C := le_trans (by norm_num : (0 : ℝ) ≤ 1) hC
  have hnorm : ‖(n, Z)‖ ≤ |n| + ‖Z‖ := by
    rw [Prod.norm_def, Real.norm_eq_abs]
    exact max_le (le_add_of_nonneg_right (norm_nonneg _)) (le_add_of_nonneg_left (abs_nonneg _))
  exact ⟨H.1.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hnorm hC0) (norm_nonneg Z)),
    H.2.1.trans (mul_le_mul_of_nonneg_left hnorm hC0), H.2.2⟩

end BianchiIX
