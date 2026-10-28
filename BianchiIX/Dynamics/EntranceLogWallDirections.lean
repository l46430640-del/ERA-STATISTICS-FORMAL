import BianchiIX.Dynamics.EntranceFullReturnColumns
import BianchiIX.Dynamics.EntranceRadialInputResponse

noncomputable section

namespace BianchiIX

theorem entrance_logWall_columns_direction {C D k L U V W : ℝ}
    {S T : ProjectiveState →L[ℝ] ℝ} {d : ProjectiveState}
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hk : 1 ≤ k) (hL : 0 ≤ L)
    (hU : 0 < U ∧ U ≤ 1) (hV : 0 < V) (hW : 0 < W ∧ W ≤ 1)
    (hs0 : |S (Pi.single 0 1)| ≤ C * L)
    (hs1 : |S (Pi.single 1 1) - 1 / U| ≤ C)
    (hs2 : |S (Pi.single 2 1)| ≤ C * k / V) (hs3 : |S (Pi.single 3 1)| ≤ C)
    (ht0 : |T (Pi.single 0 1)| ≤ C * L / k ^ 2)
    (ht1 : |T (Pi.single 1 1)| ≤ C / k ^ 2)
    (ht2 : |T (Pi.single 2 1)| ≤ C / V)
    (ht3 : |T (Pi.single 3 1) - 1 / W| ≤ C / k ^ 2)
    (hd0 : |d 0| ≤ D * k ^ 2) (hd1 : |d 1| ≤ D * k * U)
    (hd2 : |d 2| ≤ D * k * V) (hd3 : |d 3| ≤ D * k * W) :
    |S d| ≤ (3 * C + 1) * D * k ^ 2 * (1 + L) ∧
    |T d| ≤ (3 * C + 1) * D * (k + L) := by
  have hk0 : 0 < k := lt_of_lt_of_le zero_lt_one hk
  have hkk : k ≤ k ^ 2 := by nlinarith only [mul_le_mul_of_nonneg_left hk hk0.le]
  have hki : 1 / k ≤ k := (div_le_iff₀ hk0).mpr (by nlinarith only [hk, hkk])
  have hs1' : |S (Pi.single 1 1)| ≤ C + 1 / U := by
    have H := abs_sub_le (S (Pi.single 1 1)) (1 / U) 0
    rw [sub_zero, sub_zero, abs_of_pos (by positivity [hU.1] : 0 < 1 / U)] at H
    exact H.trans (add_le_add hs1 le_rfl)
  have ht3' : |T (Pi.single 3 1)| ≤ C / k ^ 2 + 1 / W := by
    have H := abs_sub_le (T (Pi.single 3 1)) (1 / W) 0
    rw [sub_zero, sub_zero, abs_of_pos (by positivity [hW.1] : 0 < 1 / W)] at H
    exact H.trans (add_le_add ht3 le_rfl)
  have hku : k * U ≤ k ^ 2 := (mul_le_of_le_one_right hk0.le hU.2).trans hkk
  have hkw : k * W ≤ k ^ 2 := (mul_le_of_le_one_right hk0.le hW.2).trans hkk
  have huk : U / k ≤ k := (div_le_div_of_nonneg_right hU.2 hk0.le).trans hki
  have hwk : W / k ≤ k := (div_le_div_of_nonneg_right hW.2 hk0.le).trans hki
  constructor
  · calc
      _ ≤ _ := clm_four_coordinate_bound S d
      _ ≤ (D * k ^ 2) * (C * L) + (D * k * U) * (C + 1 / U) +
          (D * k * V) * (C * k / V) + (D * k * W) * C := by
        exact add_le_add (add_le_add (add_le_add
          (mul_le_mul hd0 hs0 (abs_nonneg _) (by positivity))
          (mul_le_mul hd1 hs1' (abs_nonneg _) (by positivity [hU.1])))
          (mul_le_mul hd2 hs2 (abs_nonneg _) (by positivity)))
          (mul_le_mul hd3 hs3 (abs_nonneg _) (by positivity [hW.1]))
      _ = C * D * k ^ 2 * L + C * D * (k * U) + D * k + C * D * k ^ 2 + C * D * (k * W) := by
        field_simp [hU.1.ne', hV.ne', hk0.ne']
        ring
      _ ≤ C * D * k ^ 2 * L + C * D * k ^ 2 + D * k ^ 2 + C * D * k ^ 2 + C * D * k ^ 2 := by gcongr
      _ ≤ _ := by nlinarith only [mul_nonneg (by positivity : 0 ≤ (2 * C + 1) * D * k ^ 2) hL]
  · calc
      _ ≤ _ := clm_four_coordinate_bound T d
      _ ≤ (D * k ^ 2) * (C * L / k ^ 2) + (D * k * U) * (C / k ^ 2) +
          (D * k * V) * (C / V) + (D * k * W) * (C / k ^ 2 + 1 / W) := by
        exact add_le_add (add_le_add (add_le_add
          (mul_le_mul hd0 ht0 (abs_nonneg _) (by positivity))
          (mul_le_mul hd1 ht1 (abs_nonneg _) (by positivity [hU.1])))
          (mul_le_mul hd2 ht2 (abs_nonneg _) (by positivity)))
          (mul_le_mul hd3 ht3' (abs_nonneg _) (by positivity [hW.1]))
      _ = C * D * L + C * D * (U / k) + C * D * k + C * D * (W / k) + D * k := by
        field_simp [hW.1.ne', hV.ne', hk0.ne']
        ring
      _ ≤ C * D * L + C * D * k + C * D * k + C * D * k + D * k := by gcongr
      _ ≤ _ := by nlinarith only [mul_nonneg (by positivity : 0 ≤ (2 * C + 1) * D) hL]

end BianchiIX
