import BianchiIX.Statistics.GaussInverse
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Positivity

noncomputable section

namespace BianchiIX

open Finset

theorem gaussInv_lipschitz_weighted {n x y : ℝ} (hn : 0 < n) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |gaussInv n x - gaussInv n y| ≤ |x - y| / n ^ 2 := by
  have hnx : 0 < n + x := by linarith
  have hny : 0 < n + y := by linarith
  have hden : n ^ 2 ≤ (n + x) * (n + y) := by nlinarith [mul_nonneg hx hy]
  have hid : gaussInv n x - gaussInv n y = (y - x) / ((n + x) * (n + y)) := by
    unfold gaussInv
    field_simp
    ring
  rw [hid, abs_div, abs_of_pos (mul_pos hnx hny), abs_sub_comm y x]
  exact div_le_div_of_nonneg_left (abs_nonneg _) (sq_pos_of_pos hn) hden

/-- Endpoint errors control the lost length of one digit without a derivative comparison. -/
theorem gauss_branch_length_of_endpoint_error {n β E L R : ℝ}
    (hn : 0 < n) (hβ : 0 ≤ β) (hβmax : β ≤ 1 / 2)
    (hL : |L - gaussInv n (2 * β)| ≤ E / n ^ 2)
    (hR : |R - gaussInv n (1 - 2 * β)| ≤ E / n ^ 2) :
    1 / n - 1 / (n + 1) - (4 * β + 2 * E) / n ^ 2 ≤ L - R := by
  have hleft := gaussInv_lipschitz_weighted hn (by positivity : 0 ≤ 2 * β) (le_refl (0 : ℝ))
  have hright := gaussInv_lipschitz_weighted hn (by linarith : 0 ≤ 1 - 2 * β) (by norm_num : (0 : ℝ) ≤ 1)
  rw [sub_zero, abs_of_nonneg (by positivity : 0 ≤ 2 * β)] at hleft
  rw [show 1 - 2 * β - 1 = -(2 * β) by ring, abs_neg,
    abs_of_nonneg (by positivity : 0 ≤ 2 * β)] at hright
  have H1 := (abs_le.mp hleft).1
  have H2 := (abs_le.mp hright).2
  have H3 := (abs_le.mp hL).1
  have H4 := (abs_le.mp hR).2
  simp only [gaussInv, add_zero] at H1 H2 H3 H4
  have hid : (4 * β + 2 * E) / n ^ 2 = 2 * (2 * β / n ^ 2) + 2 * (E / n ^ 2) := by ring
  rw [hid]
  linarith

theorem sum_gauss_digit_lengths (N : ℕ) :
    (∑ m ∈ range N, (1 / ((m : ℝ) + 1) - 1 / ((m : ℝ) + 2))) = 1 - 1 / ((N : ℝ) + 1) := by
  induction N with
  | zero => norm_num
  | succ N ih =>
    rw [sum_range_succ, ih, Nat.cast_succ]
    ring

theorem sum_inverse_square_digits_le_two (N : ℕ) :
    (∑ m ∈ range N, 1 / ((m : ℝ) + 1) ^ 2) ≤ 2 := by
  have H (m : ℕ) : 1 / ((m : ℝ) + 1) ^ 2 ≤
      2 * (1 / ((m : ℝ) + 1) - 1 / ((m : ℝ) + 2)) := by
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have hm1 : 0 < (m : ℝ) + 1 := by positivity
    have hm2 : 0 < (m : ℝ) + 2 := by positivity
    field_simp
    nlinarith
  calc
    _ ≤ ∑ m ∈ range N, 2 * (1 / ((m : ℝ) + 1) - 1 / ((m : ℝ) + 2)) :=
      sum_le_sum (fun m _ => H m)
    _ = 2 * (1 - 1 / ((N : ℝ) + 1)) := by rw [← mul_sum, sum_gauss_digit_lengths]
    _ ≤ 2 := by
      have hn : 0 ≤ 1 / ((N : ℝ) + 1) := by positivity
      linarith

end BianchiIX
