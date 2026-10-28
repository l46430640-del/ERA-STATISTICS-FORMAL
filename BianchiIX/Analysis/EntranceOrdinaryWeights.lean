import BianchiIX.Analysis.ConnectionReturnBounds

noncomputable section

namespace BianchiIX

theorem entrance_ordinary_initial_weights {u w : ℝ} (hu : 0 < u) (hw : 0 < w) (v θ X Y : ℝ) :
    u * |X / u| + w * |Y / w| = |X| + |Y| ∧
      u * v * |X / u| + (u * v * w + θ * (v * w) ^ 2) * |Y / w| =
        v * |X| + (u * v + θ * v ^ 2 * w) * |Y| := by
  simp only [abs_div, abs_of_pos hu, abs_of_pos hw]
  constructor <;> field_simp

/-- The logarithmic waiting time disappears from both ordinary wall remainders. -/
theorem entrance_ordinary_log_weights {u v w θ : ℝ}
    (hu : 0 ≤ u ∧ u ≤ 1) (hv : 0 < v ∧ v ≤ 1) (hw : 0 ≤ w ∧ w ≤ 1)
    (hθ : 0 ≤ θ ∧ θ ≤ 1) (X Y : ℝ) :
    (-Real.log v) * (v * |X| + (u * v + θ * v ^ 2 * w) * |Y|) ≤
      |X| + 2 * |Y| := by
  have hL : 0 ≤ -Real.log v := neg_nonneg.mpr (Real.log_nonpos hv.1.le hv.2)
  have hLv : (-Real.log v) * v ≤ 1 := by simpa only [mul_comm] using mul_neg_log_le_one hv.1
  have hv2 : v ^ 2 ≤ v := by nlinarith only [mul_le_mul_of_nonneg_left hv.2 hv.1.le]
  have hS : θ * v ^ 2 * w ≤ v :=
    ((mul_le_of_le_one_right (mul_nonneg hθ.1 (sq_nonneg v)) hw.2).trans
      (mul_le_of_le_one_left (sq_nonneg v) hθ.2)).trans hv2
  have hP : u * v ≤ v := mul_le_of_le_one_left hv.1.le hu.2
  have H := mul_le_mul_of_nonneg_left (add_le_add hP hS) hL
  have H' : (-Real.log v) * (u * v + θ * v ^ 2 * w) ≤ 2 := by nlinarith only [H, hLv]
  have HX := mul_le_mul_of_nonneg_right hLv (abs_nonneg X)
  have HY := mul_le_mul_of_nonneg_right H' (abs_nonneg Y)
  nlinarith only [HX, HY]

end BianchiIX
