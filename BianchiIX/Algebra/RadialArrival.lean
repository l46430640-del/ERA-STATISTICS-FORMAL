import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section

namespace BianchiIX

theorem radial_arrival_factor_bounds {r c f : ℝ} (hr : 0 < r) (hc : c ≤ -1 / 2) (hf : f ≤ 0) :
    c + f / r < 0 ∧ 0 < c / (c + f / r) ∧ c / (c + f / r) ≤ 1 ∧
      |c / (c + f / r) - 1| ≤ 2 * |f| / r := by
  have ha : f / r ≤ 0 := div_nonpos_of_nonpos_of_nonneg hf hr.le
  have hc0 : c < 0 := by linarith only [hc]
  have hd : c + f / r < 0 := by linarith only [hc0, ha]
  have hden : (1 / 2 : ℝ) ≤ |c + f / r| := by
    rw [abs_of_neg hd]
    linarith only [hc, ha]
  refine ⟨hd, div_pos_of_neg_of_neg hc0 hd, (div_le_iff_of_neg hd).mpr ?_, ?_⟩
  · linarith only [ha]
  · have hsum : c / (c + f / r) + (f / r) / (c + f / r) = 1 := by
      rw [← add_div, div_self (ne_of_lt hd)]
    have hid : c / (c + f / r) - 1 = -((f / r) / (c + f / r)) := by linarith only [hsum]
    rw [hid, abs_neg, abs_div, abs_div, abs_of_pos hr]
    calc
      _ ≤ (|f| / r) / (1 / 2) := div_le_div_of_nonneg_left
        (div_nonneg (abs_nonneg _) hr.le) (by norm_num) hden
      _ = 2 * |f| / r := by ring

/-- The clock correction and the radius correction combine before taking absolute values. -/
theorem radial_arrival_variation {r c f q : ℝ} (hr : 0 < r) (hc : c ≤ -1 / 2) (hf : f ≤ 0) :
    q + f * (-q / (r * (c + f / r))) = c / (c + f / r) * q ∧
      |q + f * (-q / (r * (c + f / r)))| ≤ |q| := by
  obtain ⟨hd, hpos, hle, _⟩ := radial_arrival_factor_bounds hr hc hf
  have hsum : c / (c + f / r) + (f / r) / (c + f / r) = 1 := by
    rw [← add_div, div_self (ne_of_lt hd)]
  have hid : q + f * (-q / (r * (c + f / r))) = c / (c + f / r) * q := by
    calc
      _ = (1 - (f / r) / (c + f / r)) * q := by rw [← div_div]; ring
      _ = _ := by congr 1; linarith only [hsum]
  refine ⟨hid, ?_⟩
  rw [hid, abs_mul, abs_of_pos hpos]
  exact mul_le_of_le_one_left (abs_nonneg _) hle

end BianchiIX
