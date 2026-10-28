import BianchiIX.Algebra.CoreCoefficientEstimates

noncomputable section

namespace BianchiIX

theorem core_log_quotient_bound {d x y A B : ℝ} (hd : 999 / 1000 ≤ d)
    (hx : |x| ≤ A) (hy : |y| ≤ B) : |x / d - y / d ^ 2| ≤ 11 / 10 * (A + B) := by
  have hd0 : 0 < d := by linarith only [hd]
  have hA : 0 ≤ A := (abs_nonneg _).trans hx
  have hB : 0 ≤ B := (abs_nonneg _).trans hy
  have hdx : |x / d| ≤ 11 / 10 * A := by
    rw [abs_div, abs_of_pos hd0, div_le_iff₀ hd0]
    nlinarith only [hx, mul_nonneg hA (show 0 ≤ d - 10 / 11 by linarith only [hd])]
  have hdy : |y / d ^ 2| ≤ 11 / 10 * B := by
    rw [abs_div, abs_pow, abs_of_pos hd0, div_le_iff₀ (sq_pos_of_pos hd0)]
    have hsq : 10 / 11 ≤ d ^ 2 := by nlinarith only [hd]
    nlinarith only [hy, mul_nonneg hB (sub_nonneg.mpr hsq)]
  exact (abs_sub _ _).trans ((add_le_add hdx hdy).trans_eq (by ring))

theorem core_log_weak_products {r m v c : ℝ} (hr : 5 ≤ r)
    (hm : 0 ≤ m ∧ m ≤ 1 / 100) (hv : 1 ≤ v) (hc : 0 ≤ c ∧ c ≤ 1 / 100) :
    (2 * (1 + c) / r) * (m / r ^ 2) ≤ 1 / r ^ 2 ∧
      (2 * (1 + c) / r) * (2 * m / r ^ 2) ≤ 1 ∧
      (2 * (1 + c) / r) * (2 * m / (v * r ^ 2)) ≤ m / r := by
  have hr0 : 0 < r := by linarith only [hr]
  have hv0 : 0 < v := by linarith only [hv]
  have hcm : (1 + c) * m ≤ 2 * m := mul_le_mul_of_nonneg_right (by linarith only [hc.2]) hm.1
  have hr2 : 4 ≤ r ^ 2 := by nlinarith only [hr]
  constructor
  · apply (mul_le_mul_iff_of_pos_right (pow_pos hr0 3)).mp
    field_simp
    nlinarith only [hcm, hm.2, hr]
  constructor
  · have hr3 : 1 ≤ r ^ 3 := one_le_pow₀ (by linarith only [hr] : 1 ≤ r)
    apply (mul_le_mul_iff_of_pos_right (pow_pos hr0 3)).mp
    field_simp
    nlinarith only [hcm, hm.2, hr3]
  · have hvr : 4 * (1 + c) ≤ v * r ^ 2 := by
      have H := mul_le_mul_of_nonneg_right hv (sq_nonneg r)
      nlinarith only [H, hr, hc.2]
    have H := mul_le_mul_of_nonneg_right hvr hm.1
    apply (mul_le_mul_iff_of_pos_right (mul_pos hv0 (pow_pos hr0 3))).mp
    field_simp
    nlinarith only [H]

end BianchiIX
