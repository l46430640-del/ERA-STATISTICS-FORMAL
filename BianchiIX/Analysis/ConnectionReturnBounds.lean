import BianchiIX.Analysis.ConnectionAmplitudeBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic

noncomputable section

namespace BianchiIX

theorem mul_neg_log_le_one {w : ℝ} (hw : 0 < w) : w * (-Real.log w) ≤ 1 := by
  have H := mul_le_mul_of_nonneg_left (Real.one_sub_inv_le_log_of_pos hw) hw.le
  have hid : w * (1 - w⁻¹) = w - 1 := by field_simp
  rw [hid] at H
  nlinarith only [H, hw]

/-- The growing initial response has uniform endpoint scales despite the logarithmic duration. -/
theorem connection_growing_endpoint_coefficients {μ u w L : ℝ} (hμ : 4 ≤ μ)
    (hu : 0 ≤ u ∧ u ≤ (1 / 10000) / μ) (hw : 0 < w ∧ w ≤ 1 / 10000)
    (hL : w * L ≤ 1) :
    32 + 12800 * u + 96 / (μ * w) + 1024000 * L * (u + w) / μ ≤ 16 * μ / w ∧
    (12800 * u + 64 / (μ * w) + 1024000 * L * (u + w) / μ) / μ ^ 2 ≤
      200 / (μ ^ 3 * w) := by
  have hμ0 : 0 < μ := by linarith only [hμ]
  have hμne := ne_of_gt hμ0
  have hwne := ne_of_gt hw.1
  have huμ : u * μ ≤ 1 / 10000 := (le_div_iff₀ hμ0).mp hu.2
  have hus : u ≤ 1 / 40000 := by nlinarith only [huμ, hμ, hu.1]
  have hsum : u + w ≤ 1 / 8000 := by linarith only [hus, hw.2]
  have hmix : w * L * (u + w) ≤ 1 / 8000 :=
    (mul_le_mul_of_nonneg_right hL (by linarith only [hu.1, hw.1])).trans (by simpa using hsum)
  have hcross : μ * u * w ≤ 1 / 100000000 := by
    have H := mul_le_mul_of_nonneg_right huμ hw.1.le
    nlinarith only [H, hw.2]
  have hscaled : 32 * μ * w ≤ μ := by nlinarith only [hw.2, hμ0]
  constructor
  · apply (le_div_iff₀ hw.1).mpr
    apply (mul_le_mul_iff_left₀ hμ0).mp
    have hid : ((32 + 12800 * u + 96 / (μ * w) + 1024000 * L * (u + w) / μ) * w) * μ =
        32 * μ * w + 12800 * (μ * u * w) + 96 + 1024000 * (w * L * (u + w)) := by
      field_simp
    rw [hid]
    nlinarith only [hscaled, hcross, hmix, hμ]
  · apply (le_div_iff₀ (mul_pos (pow_pos hμ0 3) hw.1)).mpr
    have hid : ((12800 * u + 64 / (μ * w) + 1024000 * L * (u + w) / μ) / μ ^ 2) * (μ ^ 3 * w) =
        12800 * (μ * u * w) + 64 + 1024000 * (w * L * (u + w)) := by
      field_simp
    rw [hid]
    nlinarith only [hcross, hmix]

theorem connection_weak_clock_rate_bound {μ m u v w : ℝ} (hμ : 4 ≤ μ)
    (hm : |m - μ| ≤ 1 / 2) (hu : 0 ≤ u ∧ u ≤ 1 / 10000)
    (hv : 0 ≤ v ∧ v ≤ 1) (hw : 0 ≤ w ∧ w ≤ 1) :
    |connectionWeakClockRate m u v w| ≤ 1 + 8 / μ := by
  have hμ0 : 0 < μ := by linarith only [hμ]
  have hD := (connection_speed_bounds hμ hm hu hv hw).1
  have hD0 : 0 < connectionSpeed m u v w := by linarith only [hμ, hD]
  have hC := (connection_amplitude_base_bounds hμ hm hu hv hw).1
  have hq : |2 * (1 + coupling u v w) / connectionSpeed m u v w| ≤ 8 / μ := by
    rw [abs_div, abs_mul, abs_of_pos hD0, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    calc
      2 * |1 + coupling u v w| / connectionSpeed m u v w ≤ 4 / connectionSpeed m u v w :=
        div_le_div_of_nonneg_right (by linarith only [hC]) hD0.le
      _ ≤ 4 / (μ / 2) :=
        div_le_div_of_nonneg_left (by norm_num) (by positivity) hD
      _ = 8 / μ := by ring
  exact (abs_sub _ _).trans (by simpa [connectionWeakClockRate] using add_le_add_left hq 1)

end BianchiIX
