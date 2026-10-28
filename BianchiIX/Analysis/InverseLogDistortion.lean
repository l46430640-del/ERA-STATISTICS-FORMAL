import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

noncomputable section

namespace BianchiIX

theorem abs_log_le_twice_error {t e : ℝ} (he : e ≤ 1 / 4) (ht : |t - 1| ≤ e) :
    |Real.log t| ≤ 2 * e := by
  have he0 : 0 ≤ e := (abs_nonneg _).trans ht
  have ht0 : 0 < t := by linarith only [(abs_le.mp ht).1, he]
  have hhalf : 1 / 2 ≤ t := by linarith only [(abs_le.mp ht).1, he]
  have Hinv : 1 / t ≤ 1 + 2 * e := (div_le_iff₀ ht0).mpr (by
    nlinarith only [(abs_le.mp ht).1, mul_le_mul_of_nonneg_left hhalf he0])
  have Hlo := Real.one_sub_inv_le_log_of_pos ht0
  rw [inv_eq_one_div] at Hlo
  have Hhi := Real.log_le_sub_one_of_pos ht0
  exact abs_le.mpr ⟨by linarith only [Hlo, Hinv],
    by linarith only [Hhi, (abs_le.mp ht).2, he0]⟩

/-- Forward and inverse logarithmic distortion have equal magnitude. -/
theorem negative_derivative_log_bounds {α p e : ℝ}
    (hα : 0 < α) (hp : p < 0) (he : e ≤ 1 / 4) (herr : |α ^ 2 * p + 1| ≤ e) :
    |Real.log (|p| / (1 / α ^ 2))| + |Real.log (|p⁻¹| / α ^ 2)| ≤ 4 * e := by
  let t := α ^ 2 * |p|
  have Ht : |t - 1| ≤ e := by
    have HE : t - 1 = -(α ^ 2 * p + 1) := by rw [show t = α ^ 2 * |p| from rfl, abs_of_neg hp]; ring
    rwa [HE, abs_neg]
  have H := abs_log_le_twice_error he Ht
  have Hforward : |p| / (1 / α ^ 2) = t := by dsimp only [t]; field_simp
  have Hinverse : |p⁻¹| / α ^ 2 = t⁻¹ := by
    dsimp only [t]
    rw [abs_inv, mul_inv_rev, div_eq_mul_inv]
  rw [Hforward, Hinverse, Real.log_inv, abs_neg]
  linarith only [H]

end BianchiIX
