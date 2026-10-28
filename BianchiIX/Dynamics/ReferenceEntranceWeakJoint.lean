import BianchiIX.Dynamics.ReferenceEntranceWeakBounds
import BianchiIX.Analysis.ArcoshGapLogarithmic

noncomputable section

namespace BianchiIX

open Set MeasureTheory Filter
open scoped Topology

theorem referenceEntranceDuration_log_bounds {k v : ℝ} (hk : 1 < k) (hv : 0 < v ∧ v < 1) :
    -Real.log v / k ≤ referenceEntranceDuration k v ∧
      referenceEntranceDuration k v ≤ (1 - Real.log v) / k := by
  have H := arcoshGap_log_bounds hk hv
  rw [referenceEntranceDuration_eq]
  exact ⟨div_le_div_of_nonneg_right H.1 (by linarith), div_le_div_of_nonneg_right H.2 (by linarith)⟩

theorem referenceEntranceWeakResponse_scaled {k v : ℝ} (hk : k ≠ 0) (hv : v ≠ 0) :
    k * referenceEntranceWeakResponse k v / v ^ 2 =
      -((∫ t in 0..referenceEntranceDuration k v,
          Real.exp (-4 * t) / (referenceEntrancePhase k v t + 2) ^ 2) +
        Real.sqrt (k ^ 2 - 1) / (2 * (Real.sqrt (k ^ 2 - 1) + 2)) *
          Real.exp (-4 * referenceEntranceDuration k v)) := by
  unfold referenceEntranceWeakResponse
  field_simp

/-- A finite-parameter error bound avoids a two-parameter integral convergence argument. -/
theorem referenceEntranceWeakResponse_scaled_error {k v : ℝ} (hk : 2 ≤ k) (hv : 0 < v ∧ v < 1) :
    |k * referenceEntranceWeakResponse k v / v ^ 2 + 1 / 2| ≤
      4 / k + 2 * (-Real.log v) / k := by
  have hk0 : 0 < k := by linarith
  have hk' : 7 / 4 ≤ k := by linarith
  let T := referenceEntranceDuration k v
  let s := Real.sqrt (k ^ 2 - 1)
  let a := s / (2 * (s + 2))
  let E := Real.exp (-4 * T)
  let J := ∫ t in 0..T, Real.exp (-4 * t) / (referenceEntrancePhase k v t + 2) ^ 2
  have hT : 0 ≤ T := (referenceEntranceDuration_pos (by linarith) hv).le
  have hJ : 0 ≤ J := intervalIntegral.integral_nonneg hT (fun t _ =>
    div_nonneg (Real.exp_pos _).le (sq_nonneg _))
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have ha : a ≤ 1 / 2 := by
    apply (div_le_iff₀ (show 0 < 2 * (s + 2) by positivity)).mpr
    linarith
  have hE : E ≤ 1 := Real.exp_le_one_iff.mpr (by linarith only [hT])
  have hexp : 1 - E ≤ 4 * T := by linarith only [Real.add_one_le_exp (-4 * T)]
  have he : 1 / 2 - a = 1 / (s + 2) := by
    dsimp [a]
    field_simp
    ring
  have hs' : k / 2 ≤ s := Real.le_sqrt_of_sq_le (by nlinarith only [hk])
  have hi : 1 / (s + 2) ≤ 2 / k := by
    calc
      _ ≤ 1 / (k / 2) := div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
      _ = _ := by ring
  have hscaled : k * referenceEntranceWeakResponse k v / v ^ 2 = -(J + a * E) :=
    referenceEntranceWeakResponse_scaled hk0.ne' hv.1.ne'
  have hz : 0 ≤ k * referenceEntranceWeakResponse k v / v ^ 2 + 1 / 2 := by
    have H := mul_le_mul_of_nonneg_left (referenceEntranceWeakResponse_bounds hk' hv).1
      (div_nonneg hk0.le (sq_nonneg v))
    have hl : (k / v ^ 2) * (-(v ^ 2 / (2 * k))) = -(1 / 2 : ℝ) := by
      field_simp [hv.1.ne', hk0.ne']
    rw [hl] at H
    have hr : (k / v ^ 2) * referenceEntranceWeakResponse k v = k * referenceEntranceWeakResponse k v / v ^ 2 := by ring
    rw [hr] at H
    linarith only [H]
  rw [abs_of_nonneg hz, hscaled]
  have hterm := mul_le_mul_of_nonneg_right ha (sub_nonneg.mpr hE)
  have Htime := (referenceEntranceDuration_log_bounds (by linarith : 1 < k) hv).2
  calc
    -(J + a * E) + 1 / 2 ≤ 1 / (s + 2) + 2 * T := by nlinarith only [hJ, hterm, he, hexp]
    _ ≤ 2 / k + 2 * ((1 - Real.log v) / k) := by linarith only [hi, Htime]
    _ = _ := by ring

theorem referenceEntranceWeakResponse_joint_error {k L : ℝ} (hk : 2 ≤ k) (hL : 0 < L) :
    |k * referenceEntranceWeakResponse k (Real.exp (-L)) / Real.exp (-2 * L) + 1 / 2| ≤
      4 / k + 2 * (L / k) := by
  have hv : 0 < Real.exp (-L) ∧ Real.exp (-L) < 1 :=
    ⟨Real.exp_pos _, Real.exp_lt_one_iff.mpr (neg_neg_of_pos hL)⟩
  have H := referenceEntranceWeakResponse_scaled_error hk hv
  have he : Real.exp (-L) ^ 2 = Real.exp (-2 * L) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [he, Real.log_exp, neg_neg] at H
  simpa only [mul_div_assoc] using H

theorem tendsto_referenceEntranceWeakResponse_joint {ι : Type*} {l : Filter ι} {k L : ι → ℝ}
    (hk : Tendsto k l atTop) (hL : Tendsto L l atTop)
    (hsmall : Tendsto (fun i => L i / k i) l (𝓝 0)) :
    Tendsto (fun i => k i * referenceEntranceWeakResponse (k i) (Real.exp (-L i)) /
      Real.exp (-2 * L i)) l (𝓝 (-(1 / 2 : ℝ))) := by
  have hinv : Tendsto (fun i => 4 / k i) l (𝓝 0) := by
    simpa only [Function.comp_def, div_eq_mul_inv, mul_zero] using (tendsto_inv_atTop_zero.comp hk).const_mul 4
  have H : Tendsto (fun i => 4 / k i + 2 * (L i / k i)) l (𝓝 0) := by
    simpa only [mul_zero, add_zero] using hinv.add (hsmall.const_mul 2)
  have Herr : Tendsto (fun i =>
      |k i * referenceEntranceWeakResponse (k i) (Real.exp (-L i)) / Real.exp (-2 * L i) + 1 / 2|)
      l (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun _ => abs_nonneg _)) ?_ H
    filter_upwards [hk.eventually (eventually_ge_atTop (2 : ℝ)),
      hL.eventually (eventually_gt_atTop (0 : ℝ))] with i hki hLi
    exact referenceEntranceWeakResponse_joint_error hki hLi
  exact tendsto_iff_norm_sub_tendsto_zero.mpr
    (by simpa only [Real.norm_eq_abs, sub_neg_eq_add] using Herr)

end BianchiIX
