import BianchiIX.Algebra.ConnectionBounds

noncomputable section

namespace BianchiIX

theorem entrance_active_log_rate_bounds {k D M U V W c β m : ℝ}
    (hk : 1 ≤ k) (hD : k / 2 ≤ D) (hM : |M| ≤ 3 * k)
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hW : 0 ≤ W)
    (hc : |c| ≤ 2) (hβ : |β| ≤ 12 * k) (hm : |m| ≤ 4 * V / k) :
    |V * ((-(M + β) * m - (V - W) + β * U) / D)| ≤
        128 * (V ^ 2 / k + V * (U + W)) ∧
      |V * ((2 * c * m - 2 * M * U) / D ^ 2)| ≤
        64 * (U * V / k + V ^ 2 / k ^ 3) := by
  have hk0 : 0 < k := by linarith
  have hD0 : 0 < D := by linarith
  have hD2 : k ^ 2 / 4 ≤ D ^ 2 := by nlinarith only [hD, sq_nonneg (D - k / 2), hk0]
  have hMβ : |M + β| ≤ 15 * k := (abs_add_le _ _).trans (by linarith only [hM, hβ])
  have hdiff : |V - W| ≤ V + W := (abs_sub _ _).trans_eq (by rw [abs_of_nonneg hV, abs_of_nonneg hW])
  have hnumS : |-(M + β) * m - (V - W) + β * U| ≤ 61 * V + W + 12 * k * U := by
    calc
      _ ≤ |-(M + β) * m| + |V - W| + |β * U| :=
        (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
      _ ≤ (15 * k) * (4 * V / k) + (V + W) + (12 * k) * U := by
        simp only [abs_mul, abs_neg, abs_of_nonneg hU]
        exact add_le_add (add_le_add (mul_le_mul hMβ hm (abs_nonneg _) (by positivity)) hdiff)
          (mul_le_mul_of_nonneg_right hβ hU)
      _ = _ := by field_simp; ring
  have hnumW : |2 * c * m - 2 * M * U| ≤ 16 * V / k + 6 * k * U := by
    calc
      _ ≤ |2 * c * m| + |2 * M * U| := abs_sub _ _
      _ ≤ (2 * 2) * (4 * V / k) + (2 * (3 * k)) * U := by
        simp only [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_nonneg hU]
        exact add_le_add (mul_le_mul (mul_le_mul_of_nonneg_left hc (by norm_num)) hm (abs_nonneg _) (by norm_num))
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hM (by norm_num)) hU)
      _ = _ := by ring
  constructor
  · have H : |(-(M + β) * m - (V - W) + β * U) / D| ≤ 122 * V / k + 2 * W / k + 24 * U := by
      rw [abs_div, abs_of_pos hD0]
      exact (div_le_div₀ (by positivity) hnumS (by positivity) hD).trans_eq (by field_simp; ring)
    rw [abs_mul, abs_of_nonneg hV]
    apply (mul_le_mul_of_nonneg_left H hV).trans
    have hWk : W / k ≤ W := div_le_self hW hk
    have Hwk := mul_le_mul_of_nonneg_left hWk hV
    have HV : 0 ≤ V ^ 2 / k := by positivity
    simp only [div_eq_mul_inv] at Hwk HV ⊢
    nlinarith only [Hwk, HV, mul_nonneg hV hU, mul_nonneg hV hW]
  · have H : |(2 * c * m - 2 * M * U) / D ^ 2| ≤ 64 * V / k ^ 3 + 24 * U / k := by
      rw [abs_div, abs_of_nonneg (sq_nonneg D)]
      exact (div_le_div₀ (by positivity) hnumW (by positivity) hD2).trans_eq (by field_simp; ring)
    rw [abs_mul, abs_of_nonneg hV]
    apply (mul_le_mul_of_nonneg_left H hV).trans
    have Huv : 0 ≤ U * V / k := by positivity
    simp only [div_eq_mul_inv] at Huv ⊢
    nlinarith only [Huv]

end BianchiIX
