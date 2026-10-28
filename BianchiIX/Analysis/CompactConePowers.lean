import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

noncomputable section

namespace BianchiIX

theorem sqrt_log_small_bound {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    Real.sqrt x * (1 + |Real.log x|) ≤ 2 := by
  have hs := Real.sqrt_pos.mpr hx
  have H := Real.one_sub_inv_le_log_of_pos hs
  rw [Real.log_sqrt hx.le] at H
  have H' := mul_le_mul_of_nonneg_left H hs.le
  rw [mul_sub, mul_one, mul_inv_cancel₀ hs.ne'] at H'
  rw [abs_of_nonpos (Real.log_nonpos hx.le hx1)]
  nlinarith only [H', hs.le]

theorem compact_strong_cone_power {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hy1 : y ≤ 1) :
    Real.sqrt x * y ^ (19 / 24 : ℝ) *
      (1 + |Real.log y| + 1 / Real.sqrt x + 1 / Real.sqrt y) ≤ 4 * (x + y) ^ (19 / 24 : ℝ) := by
  have hb : 0 < x + y := add_pos hx hy
  have hsplit : y ^ (19 / 24 : ℝ) = y ^ (7 / 24 : ℝ) * Real.sqrt y := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hy]
    norm_num
  have hprod : Real.sqrt x * y ^ (7 / 24 : ℝ) ≤ (x + y) ^ (19 / 24 : ℝ) := by
    calc
      _ ≤ Real.sqrt (x + y) * (x + y) ^ (7 / 24 : ℝ) := mul_le_mul
        (Real.sqrt_le_sqrt (by linarith only [hy]))
        (Real.rpow_le_rpow hy.le (by linarith only [hx]) (by norm_num))
        (Real.rpow_nonneg hy.le _) (Real.sqrt_nonneg _)
      _ = _ := by rw [Real.sqrt_eq_rpow, ← Real.rpow_add hb]; norm_num
  have hself : y ^ (19 / 24 : ℝ) ≤ (x + y) ^ (19 / 24 : ℝ) :=
    Real.rpow_le_rpow hy.le (by linarith only [hx]) (by norm_num)
  have hid : Real.sqrt x * y ^ (19 / 24 : ℝ) *
      (1 + |Real.log y| + 1 / Real.sqrt x + 1 / Real.sqrt y) =
      (Real.sqrt x * y ^ (7 / 24 : ℝ)) * (Real.sqrt y * (1 + |Real.log y|)) +
        y ^ (19 / 24 : ℝ) + Real.sqrt x * y ^ (7 / 24 : ℝ) := by
    rw [hsplit]
    field_simp [(Real.sqrt_pos.mpr hx).ne', (Real.sqrt_pos.mpr hy).ne']
  rw [hid]
  have H := mul_le_mul_of_nonneg_left (sqrt_log_small_bound hy hy1)
    (mul_nonneg (Real.sqrt_nonneg x) (Real.rpow_nonneg hy.le (7 / 24)))
  nlinarith only [H, hprod, hself]

theorem compact_weak_cone_power {x y : ℝ} (hx : 0 ≤ x) (hy : 0 < y) (hy1 : y ≤ 1) :
    y ^ (13 / 18 : ℝ) * (1 + |Real.log y| + 1 / Real.sqrt y) ≤ 3 * (x + y) ^ (2 / 9 : ℝ) := by
  have hsplit : y ^ (13 / 18 : ℝ) = y ^ (2 / 9 : ℝ) * Real.sqrt y := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hy]
    norm_num
  have hid : y ^ (13 / 18 : ℝ) * (1 + |Real.log y| + 1 / Real.sqrt y) =
      y ^ (2 / 9 : ℝ) * (Real.sqrt y * (1 + |Real.log y|)) + y ^ (2 / 9 : ℝ) := by
    rw [hsplit]
    field_simp [(Real.sqrt_pos.mpr hy).ne']
  rw [hid]
  have H := mul_le_mul_of_nonneg_left (sqrt_log_small_bound hy hy1) (Real.rpow_nonneg hy.le (2 / 9))
  have Hp := Real.rpow_le_rpow hy.le (show y ≤ x + y by linarith only [hx]) (by norm_num : (0 : ℝ) ≤ 2 / 9)
  linarith only [H, Hp]

end BianchiIX
