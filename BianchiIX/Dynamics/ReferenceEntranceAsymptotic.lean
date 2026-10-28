import BianchiIX.Dynamics.ReferenceEntranceExponent
import Mathlib.Analysis.SpecialFunctions.Exp

noncomputable section

namespace BianchiIX

open Filter
open scoped Topology

theorem tendsto_pow_mul_exp_linear_decay {c : ℝ} (hc : 0 < c) (n : ℕ) :
    Tendsto (fun k : ℝ => k ^ n * Real.exp (-c * k)) atTop (𝓝 0) := by
  have H := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero n).comp
    (tendsto_id.const_mul_atTop hc)
  have H' := H.const_mul ((c ^ n)⁻¹)
  simp only [mul_zero] at H'
  apply H'.congr'
  filter_upwards with k
  dsimp only [Function.comp_def, id_eq]
  rw [mul_pow]
  field_simp

/-- An exponential error bound suffices for the mixed-response asymptotic; no
asymptotic expansion of arcosh is needed. -/
theorem referenceEntranceStrongResponse_scaled_error {k v : ℝ} (hk : 2 ≤ k) (hv : 0 < v ∧ v < 1) :
    |k ^ 2 / v * deriv (fun r => referenceEntranceStrongResponse r v) k - 2| ≤
      2 * (2 + 1 / v) * k ^ 2 * Real.exp (-((1 - v) / 2) * k) := by
  have hk0 : 0 < k := by linarith
  let A := referenceEntranceExponent k v
  let p := referenceEntranceExponentSlope k v
  let M := 1 / v + 1
  let E := Real.exp (-A)
  have hM : 0 ≤ M := by dsimp [M]; positivity [hv.1]
  have hE : 0 ≤ E := (Real.exp_pos _).le
  have hb := referenceEntranceExponent_bounds hk hv
  have he : E ≤ Real.exp (-((1 - v) / 2) * k) := by
    apply Real.exp_le_exp.mpr
    simpa only [neg_mul] using neg_le_neg hb.1
  have hid : k ^ 2 / v * deriv (fun r => referenceEntranceStrongResponse r v) k - 2 =
      -2 * (1 + k * p) * E := by
    rw [(hasDerivAt_referenceEntranceStrongResponse (show 1 < k by linarith) hv).deriv]
    dsimp [p, E, A]
    field_simp [hv.1.ne']
    ring
  have hpoly : |1 + k * p| ≤ (1 + M) * k ^ 2 := by
    have hkp : |k * p| ≤ k * (M * k) := by
      rw [abs_mul, abs_of_pos hk0]
      exact mul_le_mul_of_nonneg_left hb.2 hk0.le
    have H := (abs_add_le 1 (k * p)).trans (add_le_add le_rfl hkp)
    norm_num only [abs_one] at H
    have hk2 : 1 ≤ k ^ 2 := by nlinarith only [hk]
    change _ ≤ 1 + k * (M * k) at H
    nlinarith only [H, hk2]
  rw [hid, abs_mul, abs_mul, abs_of_nonneg hE]
  norm_num only [abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  calc
    _ ≤ 2 * ((1 + M) * k ^ 2) * E :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpoly (by norm_num)) hE
    _ ≤ 2 * ((1 + M) * k ^ 2) * Real.exp (-((1 - v) / 2) * k) :=
      mul_le_mul_of_nonneg_left he (by positivity)
    _ = _ := by dsimp [M]; ring

theorem tendsto_referenceEntranceStrongResponse_scaled_derivative {v : ℝ} (hv : 0 < v ∧ v < 1) :
    Tendsto (fun k : ℝ => k ^ 2 / v * deriv (fun r => referenceEntranceStrongResponse r v) k)
      atTop (𝓝 2) := by
  have hc : 0 < (1 - v) / 2 := by linarith [hv.2]
  have H := (tendsto_pow_mul_exp_linear_decay hc 2).const_mul (2 * (2 + 1 / v))
  simp only [mul_zero] at H
  have Herr : Tendsto (fun k : ℝ =>
      |k ^ 2 / v * deriv (fun r => referenceEntranceStrongResponse r v) k - 2|) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun _ => abs_nonneg _)) ?_ H
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with k hk
    simpa only [mul_assoc] using referenceEntranceStrongResponse_scaled_error hk hv
  exact tendsto_iff_norm_sub_tendsto_zero.mpr (by simpa only [Real.norm_eq_abs] using Herr)

end BianchiIX
