import BianchiIX.Dynamics.ReferenceEntranceWeakJoint

noncomputable section

namespace BianchiIX

open Filter Set
open scoped Topology

theorem real_tanh_exp_neg (x : ℝ) :
    Real.tanh x = (1 - Real.exp (-2 * x)) / (1 + Real.exp (-2 * x)) := by
  have he : Real.exp (-2 * x) = Real.exp (-x) / Real.exp x := by
    rw [← Real.exp_sub]
    congr 1
    ring
  rw [Real.tanh_eq, he]
  have hp := Real.exp_pos x
  have hn := Real.exp_pos (-x)
  field_simp

theorem tendsto_real_tanh_atTop : Tendsto Real.tanh atTop (𝓝 (1 : ℝ)) := by
  have he : Tendsto (fun x : ℝ => Real.exp (-2 * x)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, id_eq, neg_mul] using
      Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2))
  have H := ((tendsto_const_nhds (x := (1 : ℝ))).sub he).div
    ((tendsto_const_nhds (x := (1 : ℝ))).add he) (by norm_num)
  simp only [sub_zero, add_zero, div_one] at H
  exact H.congr' (Eventually.of_forall (fun x => (real_tanh_exp_neg x).symm))

theorem tendsto_arcosh_height_zero {k : ℝ} (hk : 1 < k) :
    Tendsto (fun v : ℝ => Real.arcosh (k / v)) (𝓝[>] 0) atTop := by
  have hlog : Tendsto (fun v : ℝ => -Real.log v) (𝓝[>] 0) atTop :=
    tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
  apply tendsto_atTop_mono' (𝓝[>] (0 : ℝ)) ?_
    (tendsto_atTop_add_const_right _ (Real.arcosh k) hlog)
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds (zero_lt_one : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds] with v hv0 hv1
  have H := (arcoshGap_log_bounds hk ⟨hv0, hv1⟩).1
  dsimp [arcoshGap] at H
  linarith only [H]

theorem tendsto_referenceEntranceDuration_zero {k : ℝ} (hk : 1 < k) :
    Tendsto (referenceEntranceDuration k) (𝓝[>] 0) atTop := by
  have hlog : Tendsto (fun v : ℝ => -Real.log v) (𝓝[>] 0) atTop :=
    tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
  apply tendsto_atTop_mono' (𝓝[>] (0 : ℝ)) ?_ (hlog.atTop_div_const (by linarith : 0 < k))
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds (zero_lt_one : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds] with v hv0 hv1
  exact (referenceEntranceDuration_log_bounds hk ⟨hv0, hv1⟩).1

theorem tendsto_referenceEntrancePhase_zero {k : ℝ} (hk : 1 < k) (t : ℝ) :
    Tendsto (fun v => referenceEntrancePhase k v t) (𝓝[>] 0) (𝓝 k) := by
  have HA : Tendsto (fun v => Real.arcosh (k / v) - k * t) (𝓝[>] 0) atTop := by
    simpa only [sub_eq_add_neg] using
      tendsto_atTop_add_const_right _ (-(k * t)) (tendsto_arcosh_height_zero hk)
  have H := (tendsto_real_tanh_atTop.comp HA).const_mul k
  simp only [mul_one, Function.comp_def] at H
  exact H.congr' (Eventually.of_forall (fun v => (referenceEntrancePhase_eq (by linarith) t).symm))

theorem tendsto_referenceEntranceWeak_terminal_zero {k : ℝ} (hk : 1 < k) :
    Tendsto (fun v => Real.sqrt (k ^ 2 - 1) / (2 * (Real.sqrt (k ^ 2 - 1) + 2)) *
      Real.exp (-4 * referenceEntranceDuration k v)) (𝓝[>] 0) (𝓝 0) := by
  have he : Tendsto (fun v => Real.exp (-4 * referenceEntranceDuration k v)) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Function.comp_def, neg_mul] using
      Real.tendsto_exp_neg_atTop_nhds_zero.comp
        ((tendsto_referenceEntranceDuration_zero hk).const_mul_atTop (by norm_num : (0 : ℝ) < 4))
  simpa only [mul_zero] using he.const_mul (Real.sqrt (k ^ 2 - 1) / (2 * (Real.sqrt (k ^ 2 - 1) + 2)))

end BianchiIX
