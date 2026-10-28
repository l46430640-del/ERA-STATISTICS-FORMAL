import BianchiIX.Algebra.StablePhaseResidual

noncomputable section

namespace BianchiIX

theorem stableResidual_coefficients_bound {m w : ℝ} (hm : 3 / 2 ≤ m) :
    |stableResidual4 m| ≤ 64 / (m + 1) ∧ |stableResidual3 m| ≤ 64 / (m + 1) ∧
    |stableResidual2 m w| ≤ 64 / (m + 1) ∧ |stableResidual1 m w| ≤ 64 / (m + 1) := by
  let L := m + 1
  let D := m ^ 2 - 1
  let S := stableWeakRadius m w
  have hm0 : 0 < m := by linarith
  have hL : 0 < L := by dsimp [L]; linarith
  have hL1 : 1 ≤ L := by dsimp [L]; linarith
  have hD : 0 < D := by dsimp [D]; nlinarith
  have hSL : L ≤ S := phaseNorm_ge hL.le
  have hS : 0 < S := hL.trans_le hSL
  have hsum : 0 < S + L := add_pos hS hL
  have hInv : 1 / D ≤ 2 / L := by
    apply (div_le_div_iff₀ hD hL).mpr
    dsimp [L, D]
    nlinarith [sq_nonneg (m - 3 / 2)]
  have hA : m / D ≤ 3 / L := by
    apply (div_le_div_iff₀ hD hL).mpr
    dsimp [L, D]
    nlinarith [sq_nonneg (m - 3 / 2)]
  have hB : (m ^ 2 + 1) / D ≤ 3 := by
    apply (div_le_iff₀ hD).mpr
    dsimp [D]
    nlinarith [sq_nonneg (m - 3 / 2)]
  have hInvSq : 1 / L ^ 2 ≤ 1 / L :=
    one_div_le_one_div_of_le hL (by nlinarith [sq_nonneg (L - 1)])
  have h4 : |stableResidual4 m| ≤ 12 / L := by
    have heq : |stableResidual4 m| = 2 * (m / D) * (1 / D) := by
      dsimp [stableResidual4, D]
      simp only [abs_div, abs_mul, abs_pow, abs_of_pos hm0]
      norm_num
      field_simp
    rw [heq]
    have H := mul_le_mul hA hInv (by positivity : 0 ≤ 1 / D) (by positivity : 0 ≤ 3 / L)
    calc
      _ ≤ 2 * ((3 / L) * (2 / L)) := by nlinarith only [H]
      _ = 12 * (1 / L ^ 2) := by field_simp; ring
      _ ≤ 12 * (1 / L) := mul_le_mul_of_nonneg_left hInvSq (by norm_num)
      _ = _ := by ring
  have h3 : |stableResidual3 m| ≤ 36 / L := by
    have hh : 0 ≤ 3 * m - 1 := by linarith
    have heq : |stableResidual3 m| ≤ 3 * |stableResidual4 m| := by
      unfold stableResidual3 stableResidual4
      simp only [abs_div, abs_mul, abs_pow, abs_of_nonneg hh, abs_of_pos hm0]
      norm_num
      apply (div_le_iff₀ (sq_pos_of_pos hD)).mpr
      dsimp [D] at hD ⊢
      field_simp
      nlinarith
    exact heq.trans ((mul_le_mul_of_nonneg_left h4 (by norm_num)).trans_eq (by ring))
  have hfirst : (m ^ 2 + 1) / D ^ 2 ≤ 6 / L := by
    have H := mul_le_mul hB hInv (by positivity : 0 ≤ 1 / D) (by norm_num : (0 : ℝ) ≤ 3)
    convert! H using 1 <;> field_simp
    ring
  have hroot : (S + 1) / (S * (S + L)) ≤ 2 / L := by
    apply (div_le_div_iff₀ (mul_pos hS hsum) hL).mpr
    have hS1 : 1 ≤ S := hL1.trans hSL
    nlinarith [mul_le_mul_of_nonneg_left hS1 hL.le, sq_nonneg S]
  have h2 : |stableResidual2 m w| ≤ 11 / L := by
    have heq : stableResidual2 m w = -((m ^ 2 + 1) / D ^ 2) - m / D + (S + 1) / (S * (S + L)) := by
      dsimp [stableResidual2, D, S, L]
      ring
    rw [heq]
    have H := (abs_add_le (-((m ^ 2 + 1) / D ^ 2) - m / D) ((S + 1) / (S * (S + L)))).trans
      (add_le_add (abs_sub _ _) le_rfl)
    rw [abs_neg, abs_of_nonneg (by positivity : 0 ≤ (m ^ 2 + 1) / D ^ 2),
      abs_of_nonneg (by positivity : 0 ≤ m / D), abs_of_nonneg (by positivity : 0 ≤ (S + 1) / (S * (S + L)))] at H
    simp only [div_eq_mul_inv] at H hfirst hA hroot ⊢
    linarith only [H, hfirst, hA, hroot]
  have h1 : |stableResidual1 m w| ≤ 4 / L := by
    have hlast : 1 / (S + L) ≤ 1 / L := one_div_le_one_div_of_le hL (by linarith)
    change |2 / L ^ 2 + 1 / L - 1 / (S + L)| ≤ 4 / L
    have H := abs_sub (2 / L ^ 2 + 1 / L) (1 / (S + L))
    rw [abs_of_nonneg (by positivity : 0 ≤ 2 / L ^ 2 + 1 / L),
      abs_of_nonneg (by positivity : 0 ≤ 1 / (S + L))] at H
    simp only [div_eq_mul_inv] at H hInvSq hlast ⊢
    linarith only [H, hInvSq, hlast]
  exact ⟨h4.trans (div_le_div_of_nonneg_right (by norm_num) hL.le),
    h3.trans (div_le_div_of_nonneg_right (by norm_num) hL.le),
    h2.trans (div_le_div_of_nonneg_right (by norm_num) hL.le),
    h1.trans (div_le_div_of_nonneg_right (by norm_num) hL.le)⟩

theorem stableCorrectedResidual_bound {m u w : ℝ} (hm : 3 / 2 ≤ m) :
    |stableCorrectedResidual m u w| ≤ 64 / (m + 1) * |u| * (|u| + |w|) ^ 3 := by
  obtain ⟨h4, h3, h2, h1⟩ := stableResidual_coefficients_bound (w := w) hm
  have hL : 0 < m + 1 := by linarith
  have H := (abs_add_le
    (stableResidual4 m * u ^ 4 + stableResidual3 m * u ^ 3 * w + stableResidual2 m w * u ^ 2 * w ^ 2)
    (stableResidual1 m w * u * w ^ 3)).trans
      (add_le_add ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)
  change |stableCorrectedResidual m u w| ≤ _ at H
  simp only [abs_mul, abs_pow] at H
  have H4 := mul_le_mul_of_nonneg_right h4 (by positivity : 0 ≤ |u| ^ 4)
  have H3 := mul_le_mul_of_nonneg_right h3 (by positivity : 0 ≤ |u| ^ 3 * |w|)
  have H2 := mul_le_mul_of_nonneg_right h2 (by positivity : 0 ≤ |u| ^ 2 * |w| ^ 2)
  have H1 := mul_le_mul_of_nonneg_right h1 (by positivity : 0 ≤ |u| * |w| ^ 3)
  have hpoly : |u| ^ 4 + |u| ^ 3 * |w| + |u| ^ 2 * |w| ^ 2 + |u| * |w| ^ 3 ≤
      |u| * (|u| + |w|) ^ 3 := by
    nlinarith [show 0 ≤ |u| ^ 3 * |w| by positivity, show 0 ≤ |u| ^ 2 * |w| ^ 2 by positivity]
  have hp := mul_le_mul_of_nonneg_left hpoly (by positivity : 0 ≤ 64 / (m + 1))
  nlinarith only [H, H4, H3, H2, H1, hp]

theorem stableCorrectedResidual_band_bound {m c u w : ℝ}
    (hc : 2 ≤ c) (hm : |m - c| ≤ 1 / 10) :
    |stableCorrectedResidual m u w| ≤ 128 / (c + 1) * |u| * (|u| + |w|) ^ 3 := by
  have hml := (abs_le.mp hm).1
  have hm' : 3 / 2 ≤ m := by linarith
  have hL : 0 < m + 1 := by linarith
  have hK : 0 < c + 1 := by linarith
  have hratio : 64 / (m + 1) ≤ 128 / (c + 1) := by
    apply (div_le_div_iff₀ hL hK).mpr
    linarith
  exact (stableCorrectedResidual_bound hm').trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hratio (abs_nonneg _)) (by positivity))

end BianchiIX
