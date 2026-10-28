import BianchiIX.Algebra.ExitCycleBounds

noncomputable section

namespace BianchiIX

theorem exitCycle_quotient_first_bound {α H n nᵢ Hᵢ : ℝ} (hα : 0 < α)
    (hH : 39 / 10 * α ^ 2 ≤ H) (hn : |n| ≤ 12 * α) (hni : |nᵢ| ≤ 4) (hHi : |Hᵢ| ≤ 6 * α) :
    |nᵢ / H - n * Hᵢ / H ^ 2| ≤ 6 / α ^ 2 := by
  have hH0 : 0 < H := lt_of_lt_of_le (by positivity) hH
  calc
    _ ≤ |nᵢ / H| + |n * Hᵢ / H ^ 2| := abs_sub _ _
    _ = |nᵢ| / H + |n| * |Hᵢ| / H ^ 2 := by simp only [abs_div, abs_mul, abs_pow, abs_of_pos hH0]
    _ ≤ 4 / H + (12 * α) * (6 * α) / H ^ 2 := by gcongr
    _ ≤ 4 / (39 / 10 * α ^ 2) + (12 * α) * (6 * α) / (39 / 10 * α ^ 2) ^ 2 := by gcongr
    _ = (2920 / 507 : ℝ) / α ^ 2 := by field_simp; ring
    _ ≤ 6 / α ^ 2 := div_le_div_of_nonneg_right (by norm_num) (sq_nonneg α)

theorem exitCycle_quotient_second_bound {α H n nᵢ nⱼ Hᵢ Hⱼ Hᵢⱼ : ℝ} (hα : 0 < α)
    (hH : 39 / 10 * α ^ 2 ≤ H) (hn : |n| ≤ 12 * α)
    (hni : |nᵢ| ≤ 4) (hnj : |nⱼ| ≤ 4) (hHi : |Hᵢ| ≤ 6 * α) (hHj : |Hⱼ| ≤ 6 * α)
    (hHij : |Hᵢⱼ| ≤ 2) :
    |-(nᵢ * Hⱼ + nⱼ * Hᵢ + n * Hᵢⱼ) / H ^ 2 + 2 * n * Hᵢ * Hⱼ / H ^ 3| ≤ 20 / α ^ 3 := by
  have hH0 : 0 < H := lt_of_lt_of_le (by positivity) hH
  have Hsum : |nᵢ * Hⱼ + nⱼ * Hᵢ + n * Hᵢⱼ| ≤ 72 * α := by
    have H1 := abs_add_le (nᵢ * Hⱼ + nⱼ * Hᵢ) (n * Hᵢⱼ)
    have H2 := abs_add_le (nᵢ * Hⱼ) (nⱼ * Hᵢ)
    simp only [abs_mul] at H1 H2
    have H3 := mul_le_mul hni hHj (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 4)
    have H4 := mul_le_mul hnj hHi (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 4)
    have H5 := mul_le_mul hn hHij (abs_nonneg _) (by positivity : 0 ≤ 12 * α)
    linarith only [H1, H2, H3, H4, H5]
  calc
    _ ≤ |-(nᵢ * Hⱼ + nⱼ * Hᵢ + n * Hᵢⱼ) / H ^ 2| + |2 * n * Hᵢ * Hⱼ / H ^ 3| := abs_add_le _ _
    _ = |nᵢ * Hⱼ + nⱼ * Hᵢ + n * Hᵢⱼ| / H ^ 2 + 2 * |n| * |Hᵢ| * |Hⱼ| / H ^ 3 := by
      simp only [abs_div, abs_neg, abs_mul, abs_pow, abs_of_pos hH0, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    _ ≤ 72 * α / H ^ 2 + 2 * (12 * α) * (6 * α) * (6 * α) / H ^ 3 := by gcongr
    _ ≤ 72 * α / (39 / 10 * α ^ 2) ^ 2 +
        2 * (12 * α) * (6 * α) * (6 * α) / (39 / 10 * α ^ 2) ^ 3 := by gcongr
    _ = (42400 / 2197 : ℝ) / α ^ 3 := by field_simp; ring
    _ ≤ 20 / α ^ 3 := div_le_div_of_nonneg_right (by norm_num) (pow_nonneg hα.le 3)

end BianchiIX
