import BianchiIX.Dynamics.ReferenceEntranceWeakLimitProfile
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

noncomputable section

namespace BianchiIX

open Set MeasureTheory Filter
open scoped Topology

def referenceEntranceWeakKernel (k v : ℝ) : ℝ → ℝ :=
  (Iic (referenceEntranceDuration k v)).indicator
    (fun t => Real.exp (-4 * t) / (referenceEntrancePhase k v t + 2) ^ 2)

theorem measurable_referenceEntranceWeakKernel (k v : ℝ) :
    Measurable (referenceEntranceWeakKernel k v) := by
  have hf : Measurable (fun t => Real.exp (-4 * t) / (referenceEntrancePhase k v t + 2) ^ 2) :=
    (by fun_prop : Measurable (fun t : ℝ => Real.exp (-4 * t))).div
      (((continuous_referenceEntrancePhase k v).add_const 2).pow 2).measurable
  exact hf.indicator measurableSet_Iic

theorem referenceEntranceWeakKernel_bound {k : ℝ} (hk : 7 / 4 ≤ k) (v t : ℝ) :
    ‖referenceEntranceWeakKernel k v t‖ ≤ Real.exp (-4 * t) := by
  by_cases ht : t ≤ referenceEntranceDuration k v
  · rw [referenceEntranceWeakKernel,
      indicator_of_mem (show t ∈ Iic (referenceEntranceDuration k v) from ht), Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg (Real.exp_pos _).le (sq_nonneg _))]
    have H := referenceEntrancePhase_lower hk ht
    have hd : 1 ≤ (referenceEntrancePhase k v t + 2) ^ 2 := by nlinarith [H.1, H.2]
    exact (div_le_iff₀ (lt_of_lt_of_le zero_lt_one hd)).mpr
      (le_mul_of_one_le_right (Real.exp_pos _).le hd)
  · rw [referenceEntranceWeakKernel,
      indicator_of_notMem (show t ∉ Iic (referenceEntranceDuration k v) from ht), norm_zero]
    exact (Real.exp_pos _).le

theorem tendsto_referenceEntranceWeakKernel_zero {k : ℝ} (hk : 1 < k) (t : ℝ) :
    Tendsto (fun v => referenceEntranceWeakKernel k v t) (𝓝[>] 0)
      (𝓝 (Real.exp (-4 * t) / (k + 2) ^ 2)) := by
  have H := (tendsto_const_nhds (x := Real.exp (-4 * t))).div
    (((tendsto_referenceEntrancePhase_zero hk t).add_const 2).pow 2) (by positivity)
  apply H.congr'
  filter_upwards [(tendsto_referenceEntranceDuration_zero hk).eventually (eventually_ge_atTop t)] with v hv
  dsimp only [referenceEntranceWeakKernel]
  rw [indicator_of_mem (show t ∈ Iic (referenceEntranceDuration k v) from hv)]
  rfl

/-- The moving interval becomes a cutoff on the fixed positive half-line. -/
theorem referenceEntranceWeakKernel_integral {k v : ℝ} (hT : 0 ≤ referenceEntranceDuration k v) :
    (∫ t in Ioi (0 : ℝ), referenceEntranceWeakKernel k v t) =
      ∫ t in 0..referenceEntranceDuration k v,
        Real.exp (-4 * t) / (referenceEntrancePhase k v t + 2) ^ 2 := by
  rw [referenceEntranceWeakKernel, integral_indicator measurableSet_Iic,
    Measure.restrict_restrict measurableSet_Iic, inter_comm, Ioi_inter_Iic,
    intervalIntegral.integral_of_le hT]

theorem tendsto_referenceEntranceWeak_integral_zero {k : ℝ} (hk : 7 / 4 ≤ k) :
    Tendsto (fun v => ∫ t in 0..referenceEntranceDuration k v,
      Real.exp (-4 * t) / (referenceEntrancePhase k v t + 2) ^ 2)
      (𝓝[>] 0) (𝓝 (1 / (4 * (k + 2) ^ 2))) := by
  have hk1 : 1 < k := by linarith
  have H := tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict (Ioi (0 : ℝ))) (l := 𝓝[>] (0 : ℝ))
    (F := referenceEntranceWeakKernel k)
    (f := fun t => Real.exp (-4 * t) / (k + 2) ^ 2) (fun t => Real.exp (-4 * t))
    (Eventually.of_forall (fun v => (measurable_referenceEntranceWeakKernel k v).aestronglyMeasurable))
    (Eventually.of_forall (fun v => Eventually.of_forall (fun t => referenceEntranceWeakKernel_bound hk v t)))
    (integrableOn_exp_mul_Ioi (by norm_num : (-4 : ℝ) < 0) 0)
    (Eventually.of_forall (fun t => tendsto_referenceEntranceWeakKernel_zero hk1 t))
  have HI : (∫ t in Ioi (0 : ℝ), Real.exp (-4 * t) / (k + 2) ^ 2) = 1 / (4 * (k + 2) ^ 2) := by
    rw [integral_div, integral_exp_mul_Ioi (by norm_num : (-4 : ℝ) < 0)]
    norm_num only [mul_zero, Real.exp_zero]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [HI] at H
  apply H.congr'
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds (zero_lt_one : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds] with v hv0 hv1
  exact referenceEntranceWeakKernel_integral (referenceEntranceDuration_pos hk1 ⟨hv0, hv1⟩).le

theorem tendsto_referenceEntranceWeakResponse_fixed {k : ℝ} (hk : 7 / 4 ≤ k) :
    Tendsto (fun v => referenceEntranceWeakResponse k v / v ^ 2) (𝓝[>] 0)
      (𝓝 (-1 / (4 * k * (k + 2) ^ 2))) := by
  have hk0 : 0 < k := by linarith
  have H := ((tendsto_referenceEntranceWeak_integral_zero hk).add
    (tendsto_referenceEntranceWeak_terminal_zero (by linarith : 1 < k))).const_mul (-(1 / k))
  simp only [add_zero] at H
  have hc : -(1 / k) * (1 / (4 * (k + 2) ^ 2)) = -1 / (4 * k * (k + 2) ^ 2) := by
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [hc] at H
  apply H.congr'
  filter_upwards [self_mem_nhdsWithin] with v hv
  have hv0 : 0 < v := hv
  unfold referenceEntranceWeakResponse
  field_simp [hv0.ne', hk0.ne']

end BianchiIX
