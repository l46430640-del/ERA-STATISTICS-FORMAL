import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace BianchiIX

theorem critical_phase_root_bounds {A k u w : ℝ} (hA : 0 ≤ A) (hk : 2 ≤ k)
    (hu : 0 ≤ u) (hw : 0 ≤ w) (hb : u + w ≤ 1)
    (he : |4 - k + 2 * u / k| ≤ A * (u + w) ^ 2) :
    |k - 4| ≤ (A + 1) * (u + w) ∧
      |k - 4 - u / 2| ≤ (2 * A + 1) * (u + w) ^ 2 := by
  have hk0 : 0 < k := by linarith only [hk]
  have hb0 : 0 ≤ u + w := add_nonneg hu hw
  have hb2 : (u + w) ^ 2 ≤ u + w := by nlinarith only [hb0, hb]
  have hquot : 0 ≤ 2 * u / k ∧ 2 * u / k ≤ u :=
    ⟨by positivity, (div_le_iff₀ hk0).mpr (by nlinarith only [mul_le_mul_of_nonneg_left hk hu])⟩
  have hrough : |k - 4| ≤ (A + 1) * (u + w) := by
    have H := abs_sub (2 * u / k) (4 - k + 2 * u / k)
    rw [show 2 * u / k - (4 - k + 2 * u / k) = k - 4 by ring, abs_of_nonneg hquot.1] at H
    nlinarith only [H, he, hquot.2, mul_le_mul_of_nonneg_left hb2 hA, hw]
  refine ⟨hrough, ?_⟩
  have hid : 2 * u / k - u / 2 = u * (4 - k) / (2 * k) := by field_simp; ring
  have hsmall : |2 * u / k - u / 2| ≤ (A + 1) * (u + w) ^ 2 := by
    rw [hid, abs_div, abs_mul, abs_of_nonneg hu, abs_of_pos (by positivity : 0 < 2 * k), abs_sub_comm 4 k]
    calc
      _ ≤ u * |k - 4| := div_le_self (mul_nonneg hu (abs_nonneg _)) (by linarith only [hk])
      _ ≤ (u + w) * ((A + 1) * (u + w)) := mul_le_mul (by linarith only [hw]) hrough (abs_nonneg _) hb0
      _ = _ := by ring
  have H := abs_sub (2 * u / k - u / 2) (4 - k + 2 * u / k)
  rw [show 2 * u / k - u / 2 - (4 - k + 2 * u / k) = k - 4 - u / 2 by ring] at H
  nlinarith only [H, hsmall, he]

theorem critical_phase_derivative_bounds {A k b r s t : ℝ}
    (hA : 0 ≤ A) (hk : 2 ≤ k) (hb : 0 ≤ b) (hr : 1 / 2 ≤ r)
    (hk4 : |k - 4| ≤ (A + 1) * b) (hrr : |r - 1| ≤ A * b)
    (hst : |s + 2 / k| + |t| ≤ A * b) :
    |(-s / r) - 1 / 2| + |(-t / r)| ≤ (5 * A + 2) * b := by
  have hk0 : 0 < k := by linarith only [hk]
  have hr0 : 0 < r := by linarith only [hr]
  have htwo : |2 / k - 1 / 2| ≤ (A + 1) * b := by
    have hid : 2 / k - 1 / 2 = (4 - k) / (2 * k) := by field_simp; ring
    rw [hid, abs_div, abs_of_pos (by positivity : 0 < 2 * k), abs_sub_comm 4 k]
    exact (div_le_self (abs_nonneg _) (by linarith only [hk])).trans hk4
  have hnum : |s + r / 2| ≤ |s + 2 / k| + |2 / k - 1 / 2| + |r - 1| / 2 := by
    have hid : s + r / 2 = (s + 2 / k) - (2 / k - 1 / 2) + (r - 1) / 2 := by ring
    rw [hid]
    exact (abs_add_le _ _).trans ((add_le_add (abs_sub _ _) (le_rfl)).trans_eq (by rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]))
  have hid : (-s / r) - 1 / 2 = -(s + r / 2) / r := by field_simp; ring
  rw [hid, abs_div, abs_neg, abs_div, abs_neg, abs_of_pos hr0, ← add_div]
  apply (div_le_iff₀ hr0).mpr
  have H := mul_le_mul_of_nonneg_left hr (show 0 ≤ (5 * A + 2) * b from by positivity)
  nlinarith only [hnum, htwo, hrr, hst, H]

end BianchiIX
