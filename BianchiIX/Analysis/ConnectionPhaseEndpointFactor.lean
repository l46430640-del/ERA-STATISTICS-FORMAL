import BianchiIX.Analysis.MatchingKernelDifferential

noncomputable section

namespace BianchiIX

def connectionExitPhaseFactor (m v : ℝ) : ℝ :=
  ((m - 1) / phaseNorm (m - 1) 1) / matchingPhaseSlope m v 1

/-- Eliminating the radial derivative absorbs both endpoint defect derivatives into one factor. -/
theorem connectionExitPhaseFactor_sub_one {m v : ℝ} (hm : 1 < m)
    (hf : matchingPhaseSlope m v 1 ≠ 0) :
    connectionExitPhaseFactor m v - 1 = v ^ 2 * phaseNormKernel (m + 1) v / matchingPhaseSlope m v 1 := by
  have H := phaseNorm_ratio_defect (b := v) (show 0 < m + 1 by linarith only [hm])
  rw [connectionExitPhaseFactor, div_sub_one hf]
  have hid : (m - 1) / phaseNorm (m - 1) 1 - matchingPhaseSlope m v 1 =
      1 - (m + 1) / phaseNorm (m + 1) v := by unfold matchingPhaseSlope; ring
  rw [hid, H]

theorem connectionExitPhaseFactor_bounds {μ m v : ℝ} (hμ : 4 ≤ μ)
    (hm : |m - μ| ≤ 1 / 2) (hv : 0 ≤ v ∧ v ≤ 1) :
    0 ≤ connectionExitPhaseFactor m v ∧ connectionExitPhaseFactor m v ≤ 4 / 3 ∧
    |connectionExitPhaseFactor m v - 1| ≤ 4 * v ^ 2 / μ ^ 2 ∧
    0 ≤ v ^ 2 / phaseNorm (m + 1) v ∧ v ^ 2 / phaseNorm (m + 1) v ≤ v ^ 2 / μ := by
  have hμ0 : 0 < μ := by linarith only [hμ]
  have hm1 : 1 < m := by linarith only [hμ, (abs_le.mp hm).1]
  have hf := (matchingPhase_slope_bounds hμ hm hv ⟨by norm_num, le_rfl⟩).1
  have hf0 : 0 < matchingPhaseSlope m v 1 := by linarith only [hf]
  have hr := phaseNorm_ratio_bounds (by linarith only [hμ, (abs_le.mp hm).1] : 2 ≤ m - 1)
    (show 0 ≤ (1 : ℝ) ∧ (1 : ℝ) ≤ 1 by norm_num)
  have hr0 : 0 ≤ (m - 1) / phaseNorm (m - 1) 1 := by linarith only [hr.1]
  have hK := phaseNormKernel_bounds (b := v) hμ0
    (show μ / 2 ≤ m + 1 by linarith only [hμ, (abs_le.mp hm).1])
  have hnorm : μ ≤ phaseNorm (m + 1) v :=
    (show μ ≤ m + 1 by linarith only [(abs_le.mp hm).1]).trans (phaseNorm_ge (by linarith only [hm1]))
  refine ⟨div_nonneg hr0 hf0.le, ?_, ?_, div_nonneg (sq_nonneg v) (hμ0.le.trans hnorm),
    div_le_div_of_nonneg_left (sq_nonneg v) hμ0 hnorm⟩
  · exact (div_le_iff₀ hf0).mpr (by linarith only [hr.2, hf])
  · rw [connectionExitPhaseFactor_sub_one hm1 (ne_of_gt hf0),
      abs_of_nonneg (div_nonneg (mul_nonneg (sq_nonneg v) hK.1) hf0.le)]
    have H := div_le_div_of_nonneg_left (mul_nonneg (sq_nonneg v) hK.1) (by norm_num : (0 : ℝ) < 3 / 4) hf
    calc
      v ^ 2 * phaseNormKernel (m + 1) v / matchingPhaseSlope m v 1 ≤
          v ^ 2 * phaseNormKernel (m + 1) v / (3 / 4) := H
      _ ≤ v ^ 2 * (2 / μ ^ 2) / (3 / 4) := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hK.2 (sq_nonneg v)) (by norm_num)
      _ ≤ 4 * v ^ 2 / μ ^ 2 := by
        have hq : 0 ≤ v ^ 2 / μ ^ 2 := div_nonneg (sq_nonneg v) (sq_nonneg μ)
        simp only [div_eq_mul_inv] at hq ⊢
        nlinarith only [hq]

theorem matchingPhase_entry_slope_defect {μ w : ℝ} (hμ : 4 ≤ μ) :
    |matchingPhaseSlope μ 1 w - (μ + 1) / phaseNorm (μ + 1) 1| ≤ 2 * w ^ 2 / μ ^ 2 := by
  have hμ0 : 0 < μ := by linarith only [hμ]
  have hK := phaseNormKernel_bounds (b := w) hμ0 (show μ / 2 ≤ μ - 1 by linarith only [hμ])
  have H := phaseNorm_ratio_defect (b := w) (show 0 < μ - 1 by linarith only [hμ])
  have hid : matchingPhaseSlope μ 1 w - (μ + 1) / phaseNorm (μ + 1) 1 =
      -(w ^ 2 * phaseNormKernel (μ - 1) w) := by unfold matchingPhaseSlope; linarith only [H]
  rw [hid, abs_neg, abs_of_nonneg (mul_nonneg (sq_nonneg w) hK.1)]
  exact (mul_le_mul_of_nonneg_left hK.2 (sq_nonneg w)).trans_eq (by ring)

end BianchiIX
