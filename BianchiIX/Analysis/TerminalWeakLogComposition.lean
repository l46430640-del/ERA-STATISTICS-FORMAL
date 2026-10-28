import BianchiIX.Analysis.TerminalLogComposition

noncomputable section

namespace BianchiIX

/-- Subtracting the weak diagonal before estimating preserves its leading coefficient. -/
theorem terminal_weak_log_composition_error
    (M : (Fin 4 → ℝ) →L[ℝ] (Fin 2 → ℝ)) (d : Fin 4 → ℝ)
    {A B α k u v w L t : ℝ} (hA : 1 ≤ A) (hB : 1 ≤ B)
    (hα : 0 < α ∧ α ≤ 1) (hk : 1 / α ≤ k)
    (hu : 0 < u ∧ u ≤ 1) (hv : 0 < v) (hw : 0 < w ∧ w ≤ 1)
    (hL : 0 ≤ L) (ht : 0 ≤ t) (hwt : w * t ≤ B / α ^ 2)
    (hd0 : |d 0| ≤ B / α ^ 2) (hd1 : |d 1| ≤ u * (B / α))
    (hd2 : |d 2| ≤ v * (B / α)) (hd3 : |d 3 / w - t| ≤ B / α)
    (hWr : |M (Pi.single 0 1) 1| ≤ A * L / k ^ 2)
    (hWu : |M (Pi.single 1 1) 1| ≤ A / k ^ 2)
    (hWv : |M (Pi.single 2 1) 1| ≤ A / v)
    (hWw : |M (Pi.single 3 1) 1 - 1 / w| ≤ A / k ^ 2) :
    |M d 1 - t| ≤ 5 * A * B * (L + 1 / α) := by
  have hA0 : 0 ≤ A := le_trans (by norm_num) hA
  have hB0 : 0 ≤ B := le_trans (by norm_num) hB
  have hAB : 0 ≤ A * B := mul_nonneg hA0 hB0
  have hα0 : 0 < α := hα.1
  have hu0 : 0 < u := hu.1
  have hw0 : 0 < w := hw.1
  have hk1 : 1 ≤ k := ((one_le_div hα.1).mpr hα.2).trans hk
  have hk0 : 0 < k := lt_of_lt_of_le (by norm_num) hk1
  have hk2 : 1 ≤ k ^ 2 := by nlinarith only [hk1]
  have hak : 1 ≤ α * k := by nlinarith only [(div_le_iff₀ hα.1).mp hk]
  have haksq : 1 ≤ α ^ 2 * k ^ 2 := by nlinarith only [sq_nonneg (α * k - 1), hak]
  have hkinv : 1 / k ^ 2 ≤ α ^ 2 := (div_le_iff₀ (sq_pos_of_pos hk0)).mpr (by linarith only [haksq])
  have hlin : M d 1 - t =
      d 0 * M (Pi.single 0 1) 1 + d 1 * M (Pi.single 1 1) 1 +
      d 2 * M (Pi.single 2 1) 1 + d 3 * (M (Pi.single 3 1) 1 - 1 / w) + (d 3 / w - t) := by
    have hd : d = d 0 • Pi.single 0 1 + d 1 • Pi.single 1 1 +
        d 2 • Pi.single 2 1 + d 3 • Pi.single 3 1 := by
      ext j
      fin_cases j <;> simp
    conv_lhs => rw [hd, map_add, map_add, map_add, map_smul, map_smul, map_smul, map_smul]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have H0 : |d 0 * M (Pi.single 0 1) 1| ≤ A * B * L := by
    rw [abs_mul]
    calc
      _ ≤ (B / α ^ 2) * (A * L / k ^ 2) := mul_le_mul hd0 hWr (abs_nonneg _) (by positivity)
      _ = (A * B * L / α ^ 2) * (1 / k ^ 2) := by ring
      _ ≤ (A * B * L / α ^ 2) * α ^ 2 := mul_le_mul_of_nonneg_left hkinv (by positivity)
      _ = _ := by field_simp
  have H1 : |d 1 * M (Pi.single 1 1) 1| ≤ A * B / α := by
    rw [abs_mul]
    exact (mul_le_mul (hd1.trans (mul_le_of_le_one_left (by positivity) hu.2))
      (hWu.trans (div_le_self hA0 hk2)) (abs_nonneg _) (by positivity)).trans_eq (by ring)
  have H2 : |d 2 * M (Pi.single 2 1) 1| ≤ A * B / α := by
    rw [abs_mul]
    exact (mul_le_mul hd2 hWv (abs_nonneg _) (by positivity)).trans_eq (by field_simp)
  have Hd3 : |d 3| ≤ w * (B / α + t) := by
    have H := abs_sub_le (d 3 / w) t 0
    simp only [sub_zero, abs_of_nonneg ht] at H
    have H := H.trans (add_le_add hd3 le_rfl)
    rw [abs_div, abs_of_pos hw.1] at H
    exact (div_le_iff₀ hw.1).mp H |>.trans_eq (mul_comm _ _)
  have H3 : |d 3 * (M (Pi.single 3 1) 1 - 1 / w)| ≤ A * B / α + A * B := by
    rw [abs_mul]
    calc
      _ ≤ (w * (B / α + t)) * (A / k ^ 2) := mul_le_mul Hd3 hWw (abs_nonneg _) (by positivity)
      _ = (w * (B / α)) * (A / k ^ 2) + (w * t) * (A / k ^ 2) := by ring
      _ ≤ (B / α) * A + (B / α ^ 2) * (A / k ^ 2) := add_le_add
        (mul_le_mul (mul_le_of_le_one_left (by positivity) hw.2) (div_le_self hA0 hk2)
          (by positivity) (by positivity))
        (mul_le_mul_of_nonneg_right hwt (by positivity))
      _ = A * B / α + (A * B / α ^ 2) * (1 / k ^ 2) := by ring
      _ ≤ A * B / α + (A * B / α ^ 2) * α ^ 2 := add_le_add le_rfl
        (mul_le_mul_of_nonneg_left hkinv (by positivity))
      _ = _ := by field_simp
  rw [hlin]
  have H : |d 0 * M (Pi.single 0 1) 1 + d 1 * M (Pi.single 1 1) 1 +
      d 2 * M (Pi.single 2 1) 1 + d 3 * (M (Pi.single 3 1) 1 - 1 / w) + (d 3 / w - t)| ≤
      |d 0 * M (Pi.single 0 1) 1| + |d 1 * M (Pi.single 1 1) 1| +
      |d 2 * M (Pi.single 2 1) 1| + |d 3 * (M (Pi.single 3 1) 1 - 1 / w)| + |d 3 / w - t| :=
    (abs_add_le _ _).trans (add_le_add
    ((abs_add_le _ _).trans (add_le_add
      ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)) le_rfl)
  have HB : B / α ≤ A * B / α := div_le_div_of_nonneg_right
    (by nlinarith only [mul_le_mul_of_nonneg_right hA hB0]) hα.1.le
  have HAB : A * B ≤ A * B / α := (le_div_iff₀ hα.1).mpr (mul_le_of_le_one_right hAB hα.2)
  simp only [div_eq_mul_inv] at H H0 H1 H2 H3 hd3 HB HAB ⊢
  nlinarith only [H, H0, H1, H2, H3, hd3, HB, HAB, mul_nonneg hAB hL]

end BianchiIX
