import BianchiIX.Analysis.ExitTailRateDifferential

noncomputable section

namespace BianchiIX

theorem exitTailWallRate_direction_bound {v : ℝ} {Y : ExitTailState}
    (hR : 7 / 4 ≤ Y 0 ∧ Y 0 ≤ 17 / 4) (hu : |Y 1| ≤ 1 / 100)
    (hv : 0 ≤ v ∧ v ≤ 1) (hw : |Y 2| ≤ 1 / 100) (ξ : ExitTailState) (i : Fin 2) :
    |fderiv ℝ (exitTailWallRate v) Y ξ i| ≤
      512 * |ξ 0| + 256 * (v + |Y 1| + |Y 2|) * (|ξ 1| + |ξ 2|) := by
  have hvR : v ^ 2 < (Y 0) ^ 2 := by nlinarith only [hR.1, hv.1, hv.2]
  have hd : exitTailSpeed (Y 0) (Y 1) v (Y 2) ≠ 0 := by
    have H := exitTailSpeed_compact hR.1 hu hv hw
    linarith only [H]
  rw [exitTailWallRate_fderiv hvR hd, Fin.sum_univ_three]
  have HG := exitTailRateGradient_bounds hR hu hv hw i
  have H0 := mul_le_mul_of_nonneg_right HG.1 (abs_nonneg (ξ 0))
  have H1 := mul_le_mul_of_nonneg_right (HG.2 0) (abs_nonneg (ξ 1))
  have H2 := mul_le_mul_of_nonneg_right (HG.2 1) (abs_nonneg (ξ 2))
  have H := abs_add_three (exitTailRateGradient v Y i 0 * ξ 0)
    (exitTailRateGradient v Y i 1 * ξ 1) (exitTailRateGradient v Y i 2 * ξ 2)
  simp only [abs_mul] at H
  change |exitTailRateGradient v Y i 1| * |ξ 1| ≤ _ at H1
  change |exitTailRateGradient v Y i 2| * |ξ 2| ≤ _ at H2
  nlinarith only [H, H0, H1, H2]

theorem exitTailWallRate_direction_norm_bound {v : ℝ} {Y : ExitTailState}
    (hR : 7 / 4 ≤ Y 0 ∧ Y 0 ≤ 17 / 4) (hu : |Y 1| ≤ 1 / 100)
    (hv : 0 ≤ v ∧ v ≤ 1) (hw : |Y 2| ≤ 1 / 100) (ξ : ExitTailState) (i : Fin 2) :
    |fderiv ℝ (exitTailWallRate v) Y ξ i| ≤ 1536 * ‖ξ‖ := by
  have H := exitTailWallRate_direction_bound hR hu hv hw ξ i
  have hξ (j : Fin 3) : |ξ j| ≤ ‖ξ‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm ξ j
  have hp : 256 * (v + |Y 1| + |Y 2|) ≤ 512 := by linarith only [hv.2, hu, hw]
  have hm := mul_le_mul_of_nonneg_right hp (add_nonneg (abs_nonneg (ξ 1)) (abs_nonneg (ξ 2)))
  nlinarith only [H, hm, hξ 0, hξ 1, hξ 2]

end BianchiIX
