import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

/-- The logarithmic cutoff fits the fixed-domain budgets at all sufficiently small positive scales. -/
theorem eventually_restart_cutoff_budget (C C₀ q : ℝ) :
    ∀ᶠ ρ : ℝ in 𝓝[>] 0, (0 < ρ ∧ ρ ≤ 1) ∧ 2 * C₀ * ρ ≤ 1 / 16 ∧
      C * (2 * C₀ * ρ) * (q / 2 * Real.log (1 / ρ)) ≤ 1 / 8 := by
  have HI : Tendsto (fun ρ : ℝ => ρ) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have HL : Tendsto (fun ρ : ℝ => ρ * Real.log ρ) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Real.rpow_one, mul_comm] using tendsto_log_mul_rpow_nhdsGT_zero zero_lt_one
  have HB : Tendsto (fun ρ : ℝ => 2 * C₀ * ρ) (𝓝[>] 0) (𝓝 0) := by
    simpa only [mul_zero] using HI.const_mul (2 * C₀)
  have HT : Tendsto (fun ρ : ℝ => C * (2 * C₀ * ρ) * (q / 2 * Real.log (1 / ρ))) (𝓝[>] 0) (𝓝 0) := by
    convert! HL.const_mul (-C * C₀ * q) using 1
    · ext ρ
      rw [one_div, Real.log_inv]
      ring
    · simp
  filter_upwards [show ∀ᶠ ρ : ℝ in 𝓝[>] 0, 0 < ρ from self_mem_nhdsWithin,
    HI.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    HB.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 16)),
    HT.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 8))] with ρ hρ hρ1 hb ht
  exact ⟨⟨hρ, hρ1.le⟩, hb.le, ht.le⟩

/-- The explicit cutoff remainders imply the two logarithmic scales in (E.1). -/
theorem restart_cutoff_scale_bounds {C C₀ h ρ q : ℝ}
    (hC : 0 ≤ C) (hC₀ : 0 ≤ C₀) (hh : 0 ≤ h) (hρ : 0 < ρ ∧ ρ ≤ 1) (hq : 1 ≤ q) :
    (4 * C * C₀ ^ 2 * ρ ^ 2 * (q / 2 * Real.log (1 / ρ)) + 6 * h * C₀ * ρ ^ (q + 1) ≤
      (2 * C * C₀ ^ 2 * q + 6 * h * C₀) * ρ ^ 2 * (1 + |Real.log ρ|)) ∧
    (8 * C * C₀ * ρ * (q / 2 * Real.log (1 / ρ)) + 6 * h * ρ ^ q ≤
      (4 * C * C₀ * q + 6 * h) * ρ * (1 + |Real.log ρ|)) := by
  have hρ0 : 0 < ρ := hρ.1
  have hq0 : 0 ≤ q := zero_le_one.trans hq
  have hlog : Real.log (1 / ρ) = |Real.log ρ| := by
    rw [one_div, Real.log_inv, abs_of_nonpos (Real.log_nonpos hρ0.le hρ.2)]
  have hp2 : ρ ^ (q + 1) ≤ ρ ^ 2 := by
    simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_ge hρ0 hρ.2
      (by linarith only [hq] : (2 : ℝ) ≤ q + 1)
  have hp1 : ρ ^ q ≤ ρ := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge hρ0 hρ.2 hq
  constructor
  · have H := mul_le_mul_of_nonneg_left hp2 (by positivity : 0 ≤ 6 * h * C₀)
    have Hextra : 0 ≤ (2 * C * C₀ ^ 2 * q) * ρ ^ 2 + (6 * h * C₀) * ρ ^ 2 * |Real.log ρ| := by positivity
    rw [hlog]
    nlinarith only [H, Hextra]
  · have H := mul_le_mul_of_nonneg_left hp1 (by positivity : 0 ≤ 6 * h)
    have Hextra : 0 ≤ (4 * C * C₀ * q) * ρ + (6 * h) * ρ * |Real.log ρ| := by positivity
    rw [hlog]
    nlinarith only [H, Hextra]

end BianchiIX
