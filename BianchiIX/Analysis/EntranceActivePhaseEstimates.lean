import BianchiIX.Algebra.ConnectionBounds

noncomputable section

namespace BianchiIX

theorem entrance_weak_active_quotient_bound {k r D b U V m N B A C : ℝ}
    (hk : 1 ≤ k) (hrD : k ^ 2 / 4 ≤ r * D) (hD : k / 2 ≤ D)
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hm : |m| ≤ 4 * V / k) (hN : |N| ≤ A * b ^ 2 / k ^ 2)
    (hB : |B| ≤ C * b ^ 2 / k ^ 2) :
    |N * m / (r * D) - B * ((m - U) / D)| ≤
      (16 * A + 10 * C) * b ^ 2 * (V / k ^ 4 + U / k ^ 3) := by
  have hk0 : 0 < k := by linarith
  have hD0 : 0 < D := by linarith
  have hrD0 : 0 < r * D := lt_of_lt_of_le (by positivity) hrD
  have hnm : |N * m / (r * D)| ≤ 16 * A * b ^ 2 * V / k ^ 5 := by
    rw [abs_div, abs_mul, abs_of_pos hrD0]
    exact (div_le_div₀ (by positivity)
      (mul_le_mul hN hm (abs_nonneg _) (by positivity)) (by positivity) hrD).trans_eq (by field_simp; ring)
  have hmd : |(m - U) / D| ≤ 8 * V / k ^ 2 + 2 * U / k := by
    rw [abs_div, abs_of_pos hD0]
    have H : |m - U| ≤ 4 * V / k + U :=
      (abs_sub _ _).trans (add_le_add hm (abs_of_nonneg hU).le)
    exact (div_le_div₀ (by positivity) H (by positivity) hD).trans_eq (by field_simp; ring)
  have hnm' : 16 * A * b ^ 2 * V / k ^ 5 ≤ 16 * A * b ^ 2 * V / k ^ 4 :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) (pow_le_pow_right₀ hk (by norm_num : 4 ≤ 5))
  calc
    _ ≤ |N * m / (r * D)| + |B| * |(m - U) / D| := by
      simpa only [abs_mul] using abs_sub (N * m / (r * D)) (B * ((m - U) / D))
    _ ≤ 16 * A * b ^ 2 * V / k ^ 4 + (C * b ^ 2 / k ^ 2) * (8 * V / k ^ 2 + 2 * U / k) :=
      add_le_add (hnm.trans hnm') (mul_le_mul hB hmd (abs_nonneg _) (by positivity))
    _ ≤ _ := by
      apply le_of_sub_nonneg
      calc
        0 ≤ 16 * (A * b ^ 2 * (U / k ^ 3)) + 8 * (C * b ^ 2 * (U / k ^ 3)) +
            2 * (C * b ^ 2 * (V / k ^ 4)) := by positivity
        _ = _ := by field_simp; ring

theorem entrance_active_drift_bound {k U V W A AV B BV S T R : ℝ}
    (hk : 1 ≤ k) (hU : 0 ≤ U) (hV : 0 ≤ V) (hV1 : V ≤ 1) (hW : 0 ≤ W)
    (hb1 : U + W ≤ 1) (hS : 0 ≤ S) (hT : 0 ≤ T) (hR : 0 ≤ R)
    (hA : |A| + |AV| ≤ S)
    (hB : |B| ≤ T * (U * (U + W) / k ^ 2 + W ^ 2 / k ^ 4))
    (hBV : |BV| ≤ R * (U + W) ^ 2 * (V / k ^ 4 + U / k ^ 3)) :
    |V * (U * A + U * V * AV + 2 * V * B + V ^ 2 * BV)| ≤
      (S + 2 * T + 3 * R) * (U * V + V ^ 2 * W ^ 2 / k ^ 4) := by
  have hk0 : 0 < k := by linarith
  have hb : 0 ≤ U + W := add_nonneg hU hW
  have hb2 : (U + W) ^ 2 ≤ 1 := pow_le_one₀ hb hb1
  have hV2 : V ^ 2 ≤ V := by nlinarith only [hV, hV1]
  have hV3 : V ^ 3 ≤ V := (pow_le_pow_of_le_one hV hV1 (by norm_num : 1 ≤ 3)).trans_eq (pow_one V)
  have hV4 : V ^ 4 ≤ V ^ 2 := pow_le_pow_of_le_one hV hV1 (by norm_num : 2 ≤ 4)
  have hquad : (U + W) ^ 2 ≤ 2 * U + W ^ 2 := by
    nlinarith only [mul_le_mul_of_nonneg_left hb1 hU, sq_nonneg U]
  have hA' : |U * A + U * V * AV| ≤ U * S := by
    calc
      _ ≤ U * |A| + U * V * |AV| := by simpa only [abs_mul, abs_of_nonneg hU, abs_of_nonneg hV] using abs_add_le (U * A) (U * V * AV)
      _ ≤ U * |A| + U * |AV| := add_le_add le_rfl
        (mul_le_mul_of_nonneg_right (mul_le_of_le_one_right hU hV1) (abs_nonneg _))
      _ = U * (|A| + |AV|) := by ring
      _ ≤ U * S := mul_le_mul_of_nonneg_left hA hU
  have hp : V ^ 2 * U * (U + W) / k ^ 2 ≤ U * V := by
    calc
      _ ≤ V ^ 2 * U * (U + W) := div_le_self (by positivity) (one_le_pow₀ hk)
      _ ≤ V ^ 2 * U := mul_le_of_le_one_right (by positivity) hb1
      _ ≤ _ := (mul_le_mul_of_nonneg_right hV2 hU).trans_eq (mul_comm _ _)
  have hp4 : V ^ 4 * U / k ^ 4 ≤ U * V := by
    calc
      _ ≤ V ^ 4 * U := div_le_self (by positivity) (one_le_pow₀ hk)
      _ ≤ V * U := mul_le_mul_of_nonneg_right (hV4.trans hV2) hU
      _ = _ := mul_comm _ _
  have hw4 : V ^ 4 * W ^ 2 / k ^ 4 ≤ V ^ 2 * W ^ 2 / k ^ 4 :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hV4 (sq_nonneg W)) (by positivity)
  have hq4 : V ^ 4 * (U + W) ^ 2 / k ^ 4 ≤ 2 * (U * V) + V ^ 2 * W ^ 2 / k ^ 4 := by
    calc
      _ ≤ V ^ 4 * (2 * U + W ^ 2) / k ^ 4 := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hquad (by positivity)) (by positivity)
      _ = 2 * (V ^ 4 * U / k ^ 4) + V ^ 4 * W ^ 2 / k ^ 4 := by ring
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hp4 (by norm_num)) hw4
  have hq3 : U * V ^ 3 * (U + W) ^ 2 / k ^ 3 ≤ U * V := by
    calc
      _ ≤ U * V ^ 3 * (U + W) ^ 2 := div_le_self (by positivity) (one_le_pow₀ hk)
      _ ≤ U * V ^ 3 := mul_le_of_le_one_right (by positivity) hb2
      _ ≤ _ := mul_le_mul_of_nonneg_left hV3 hU
  have hlead := mul_le_mul_of_nonneg_left hA' hV
  have hweak := mul_le_mul_of_nonneg_left hB (show 0 ≤ 2 * V ^ 2 by positivity)
  have htail := mul_le_mul_of_nonneg_left hBV (show 0 ≤ V ^ 3 by positivity)
  have H : |V * (U * A + U * V * AV + 2 * V * B + V ^ 2 * BV)| ≤
      S * (U * V) + 2 * T * (U * V + V ^ 2 * W ^ 2 / k ^ 4) +
        R * (3 * (U * V) + V ^ 2 * W ^ 2 / k ^ 4) := by
    calc
      _ ≤ V * |U * A + U * V * AV| + 2 * V ^ 2 * |B| + V ^ 3 * |BV| := by
        rw [abs_mul, abs_of_nonneg hV]
        have H := mul_le_mul_of_nonneg_left ((abs_add_le (U * A + U * V * AV + 2 * V * B) (V ^ 2 * BV)).trans
          (add_le_add (abs_add_le (U * A + U * V * AV) _) le_rfl)) hV
        simp only [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_nonneg hV,
          abs_of_nonneg (sq_nonneg V)] at H
        convert! H using 1
        ring
      _ ≤ V * (U * S) + 2 * V ^ 2 * (T * (U * (U + W) / k ^ 2 + W ^ 2 / k ^ 4)) +
          V ^ 3 * (R * (U + W) ^ 2 * (V / k ^ 4 + U / k ^ 3)) := add_le_add (add_le_add hlead hweak) htail
      _ = S * (U * V) + 2 * T * (V ^ 2 * U * (U + W) / k ^ 2 + V ^ 2 * W ^ 2 / k ^ 4) +
          R * (V ^ 4 * (U + W) ^ 2 / k ^ 4 + U * V ^ 3 * (U + W) ^ 2 / k ^ 3) := by ring
      _ ≤ _ := add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left (add_le_add hp le_rfl) (by positivity)))
        (mul_le_mul_of_nonneg_left ((add_le_add hq4 hq3).trans_eq (by ring)) hR)
  apply H.trans
  have hX : 0 ≤ V ^ 2 * W ^ 2 / k ^ 4 := by positivity
  nlinarith only [mul_nonneg hS hX, mul_nonneg hR hX]

end BianchiIX
