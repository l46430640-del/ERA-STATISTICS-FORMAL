import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

noncomputable section

namespace BianchiIX

/-- A small logarithmic ratio controls the ordinary relative error without a lower bound on the scale. -/
theorem abs_sub_le_of_log_ratio {a b r : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hr : |Real.log (a / b)| ≤ r) (hr1 : r ≤ 1) : |a - b| ≤ 2 * r * b := by
  have H := Real.abs_exp_sub_one_le (hr.trans hr1)
  rw [Real.exp_log (div_pos ha hb)] at H
  have H' := mul_le_mul_of_nonneg_right (H.trans (mul_le_mul_of_nonneg_left hr (by norm_num))) hb.le
  have heq : (a / b - 1) * b = a - b := by field_simp
  rw [← heq, abs_mul, abs_of_pos hb]
  exact H'

end BianchiIX
