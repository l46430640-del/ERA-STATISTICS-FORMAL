import BianchiIX.Analysis.ConnectionEndpointScales
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section

namespace BianchiIX

theorem entrance_weak_weight_eq_rpow {v : ℝ} (hv : 0 < v) (k : ℝ) :
    Real.exp (-2 * (-Real.log v) / k) = v ^ (2 / k) := by
  rw [Real.rpow_def_of_pos hv]
  congr 1
  ring

theorem entrance_terminal_clock_weights {k L : ℝ} (hk : 1 ≤ k) (hL : 0 ≤ L) :
    (0 ≤ Real.exp (-k * L / 3) ∧ Real.exp (-k * L / 3) ≤ 1) ∧
    (0 ≤ Real.exp (-L / k) ∧ Real.exp (-L / k) ≤ 1) ∧
    L * Real.exp (-k * L / 3) ≤ 3 / k ∧
    Real.exp (-L / k) ^ 2 = Real.exp (-2 * L / k) ∧
    (1 + L / k) * Real.exp (-2 * L / k) ≤ 1 := by
  have hk0 : 0 < k := by linarith
  refine ⟨⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr (by nlinarith only [mul_nonneg hk0.le hL])⟩,
    ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hL) hk0.le)⟩, ?_, ?_, ?_⟩
  · have H := affine_mul_exp_neg_le_one (k * L / 3)
    rw [show -(k * L / 3) = -k * L / 3 by ring] at H
    apply (le_div_iff₀ hk0).mpr
    nlinarith only [H, Real.exp_pos (-k * L / 3)]
  · rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  · have H := affine_mul_exp_neg_le_one (2 * L / k)
    rw [show -(2 * L / k) = -2 * L / k by ring] at H
    have hcoeff : 1 + L / k ≤ 1 + 2 * L / k := by
      rw [mul_div_assoc]
      linarith only [div_nonneg hL hk0.le]
    exact (mul_le_mul_of_nonneg_right hcoeff (Real.exp_pos _).le).trans H

end BianchiIX
