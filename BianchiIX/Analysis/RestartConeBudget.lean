import BianchiIX.Analysis.RestartCoreBudget
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

theorem restart_core_sqrt_amplitude_bounds {r h M q ζ U p : ℝ}
    (hr : 0 < r) (hh : 0 ≤ h) (hM : 0 ≤ M) (hζ : 0 ≤ ζ)
    (hU : 0 ≤ U ∧ U ≤ 32 * h * r ^ (q - 2))
    (hp : 0 ≤ p ∧ p ≤ 2048 * M * ζ / r ^ 3) :
    Real.sqrt U ≤ Real.sqrt (32 * h) * r ^ ((q - 2) / 2) ∧
      r * Real.sqrt p ≤ Real.sqrt (2048 * M) * Real.sqrt (ζ / r) := by
  have hrpow : Real.sqrt (r ^ (q - 2)) = r ^ ((q - 2) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hr.le]
    congr 1
    ring
  refine ⟨?_, ?_⟩
  · simpa only [Real.sqrt_mul (by positivity : 0 ≤ 32 * h), hrpow] using Real.sqrt_le_sqrt hU.2
  · apply (sq_le_sq₀ (by positivity : 0 ≤ r * Real.sqrt p) (by positivity)).mp
    rw [mul_pow, Real.sq_sqrt hp.1, mul_pow,
      Real.sq_sqrt (by positivity : 0 ≤ 2048 * M), Real.sq_sqrt (div_nonneg hζ hr.le)]
    have H := mul_le_mul_of_nonneg_left hp.2 (sq_nonneg r)
    exact H.trans_eq (by field_simp)

theorem restart_core_sqrt_budget {r h M q ζ U p CU CP C : ℝ}
    (hr : 0 < r) (hh : 0 ≤ h) (hM : 0 ≤ M) (hζ : 0 ≤ ζ)
    (hU : 0 ≤ U ∧ U ≤ 32 * h * r ^ (q - 2))
    (hp : 0 ≤ p ∧ p ≤ 2048 * M * ζ / r ^ 3)
    (hCU : 0 ≤ CU) (hCP : 0 ≤ CP)
    (hC : CU * Real.sqrt (32 * h) + CP * Real.sqrt (2048 * M) ≤ C) :
    CU * Real.sqrt U + CP * r * Real.sqrt p ≤
      C * (r ^ ((q - 2) / 2) + Real.sqrt (ζ / r)) := by
  obtain ⟨HU, HP⟩ := restart_core_sqrt_amplitude_bounds hr hh hM hζ hU hp
  have H₁ := mul_le_mul_of_nonneg_left HU hCU
  have H₂ := mul_le_mul_of_nonneg_left HP hCP
  have Hcross₁ := mul_nonneg (mul_nonneg hCU (Real.sqrt_nonneg (32 * h))) (Real.sqrt_nonneg (ζ / r))
  have Hcross₂ := mul_nonneg (mul_nonneg hCP (Real.sqrt_nonneg (2048 * M))) (Real.rpow_nonneg hr.le ((q - 2) / 2))
  have HC := mul_le_mul_of_nonneg_right hC (show 0 ≤ r ^ ((q - 2) / 2) + Real.sqrt (ζ / r) by positivity)
  nlinarith only [H₁, H₂, Hcross₁, Hcross₂, HC]

theorem restart_weak_sqrt_power {r ζ P : ℝ} (hr : 0 < r) (hζ : 0 ≤ ζ ∧ ζ ≤ r ^ P) :
    Real.sqrt (ζ / r) ≤ r ^ ((P - 1) / 2) := by
  have H : ζ / r ≤ r ^ (P - 1) := by
    rw [Real.rpow_sub hr, Real.rpow_one]
    exact div_le_div_of_nonneg_right hζ.2 hr.le
  have heq : Real.sqrt (r ^ (P - 1)) = r ^ ((P - 1) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hr.le]
    congr 1
    ring
  exact (Real.sqrt_le_sqrt H).trans_eq heq

theorem eventually_restart_core_cone_budget {C q P δ : ℝ}
    (hC : 0 ≤ C) (hq : 2 < q) (hP : 1 < P) (hδ : 0 < δ) :
    ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ ζ : ℝ, 0 ≤ ζ ∧ ζ ≤ r ^ P →
      C * (r ^ ((q - 2) / 2) + Real.sqrt (ζ / r)) ≤ δ := by
  have hqpos : 0 < (q - 2) / 2 := by linarith only [hq]
  have hPpos : 0 < (P - 1) / 2 := by linarith only [hP]
  have Hq := (Real.continuous_rpow_const hqpos.le).continuousAt (x := (0 : ℝ))
  have HP := (Real.continuous_rpow_const hPpos.le).continuousAt (x := (0 : ℝ))
  have H : ContinuousAt (fun r : ℝ => C * (r ^ ((q - 2) / 2) + r ^ ((P - 1) / 2))) 0 :=
    continuousAt_const.mul (Hq.add HP)
  have Hzero : C * ((0 : ℝ) ^ ((q - 2) / 2) + (0 : ℝ) ^ ((P - 1) / 2)) < δ := by
    simpa only [Real.zero_rpow hqpos.ne', Real.zero_rpow hPpos.ne', add_zero, mul_zero] using hδ
  have HE : ∀ᶠ r : ℝ in 𝓝[>] 0,
      C * (r ^ ((q - 2) / 2) + r ^ ((P - 1) / 2)) < δ :=
    (H.eventually (isOpen_Iio.mem_nhds Hzero)).filter_mono nhdsWithin_le_nhds
  filter_upwards [HE, self_mem_nhdsWithin] with r hr hrpos
  intro ζ hζ
  exact (mul_le_mul_of_nonneg_left (add_le_add le_rfl (restart_weak_sqrt_power hrpos hζ)) hC).trans hr.le

end BianchiIX
