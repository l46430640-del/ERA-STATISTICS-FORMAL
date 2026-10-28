import BianchiIX.Dynamics.ReferenceEntranceExponent

noncomputable section

namespace BianchiIX

open Filter Set
open scoped Topology

def referenceEntranceHeightResponse (k v : ℝ) : ℝ :=
  -2 / k * (1 - Real.exp (-referenceEntranceExponent k v)) +
    k * Real.exp (-referenceEntranceExponent k v) / Real.sqrt (k ^ 2 - v ^ 2)

theorem hasDerivAt_referenceEntranceExponent_height {k v : ℝ}
    (hk : 1 < k) (hv : 0 < v ∧ v < 1) :
    HasDerivAt (referenceEntranceExponent k)
      (-(k ^ 2) / (2 * v * Real.sqrt (k ^ 2 - v ^ 2))) v := by
  have hkv : 1 < k / v := (one_lt_div hv.1).mpr (hv.2.trans hk)
  have H := (((Real.hasDerivAt_arcosh hkv).comp v
    ((hasDerivAt_const v k).div (hasDerivAt_id v) hv.1.ne')).sub_const (Real.arcosh k)).const_mul (k / 2)
  convert! H using 1
  rw [sqrt_scaled_gap hk hv]
  field_simp [hv.1.ne']
  ring

theorem hasDerivAt_referenceEntranceStrongResponse_height {k v : ℝ}
    (hk : 1 < k) (hv : 0 < v ∧ v < 1) :
    HasDerivAt (referenceEntranceStrongResponse k) (referenceEntranceHeightResponse k v) v := by
  have he := (hasDerivAt_referenceEntranceExponent_height hk hv).neg.exp
  have H := (((hasDerivAt_id v).const_mul (-2)).div_const k).mul (he.const_sub 1)
  convert! H using 1
  · ext w
    exact referenceEntranceStrongResponse_exponent k w
  · dsimp [referenceEntranceHeightResponse]
    field_simp [hv.1.ne']

theorem continuousAt_referenceEntranceHeightResponse_one {k : ℝ} (hk : 1 < k) :
    ContinuousAt (referenceEntranceHeightResponse k) 1 := by
  have hdiv : ContinuousAt (fun v : ℝ => k / v) 1 :=
    continuousAt_const.div continuousAt_id one_ne_zero
  have hac : ContinuousAt Real.arcosh (k / (1 : ℝ)) :=
    by simpa using (Real.differentiableAt_arcosh hk).continuousAt
  have hA : ContinuousAt (referenceEntranceExponent k) 1 :=
    continuousAt_const.mul ((hac.comp hdiv).sub continuousAt_const)
  have hs : Real.sqrt (k ^ 2 - (1 : ℝ) ^ 2) ≠ 0 :=
    (Real.sqrt_pos.mpr (by nlinarith only [hk])).ne'
  have he : ContinuousAt (fun v => Real.exp (-referenceEntranceExponent k v)) 1 :=
    Real.continuous_exp.continuousAt.comp hA.neg
  exact (continuousAt_const.mul (continuousAt_const.sub he)).add
    ((continuousAt_const.mul he).div ((continuousAt_const.sub (continuousAt_id.pow 2)).sqrt) hs)

theorem referenceEntranceHeightResponse_one (k : ℝ) :
    referenceEntranceHeightResponse k 1 = k / Real.sqrt (k ^ 2 - 1) := by
  simp [referenceEntranceHeightResponse, referenceEntranceExponent, arcoshGap]

theorem tendsto_referenceEntranceHeightResponse_one {k : ℝ} (hk : 1 < k) :
    Tendsto (referenceEntranceHeightResponse k) (𝓝[<] 1) (𝓝 (k / Real.sqrt (k ^ 2 - 1))) := by
  simpa only [referenceEntranceHeightResponse_one] using
    (continuousAt_referenceEntranceHeightResponse_one hk).tendsto.mono_left nhdsWithin_le_nhds

theorem tendsto_referenceEntranceStrongResponse_height_derivative {k : ℝ} (hk : 1 < k) :
    Tendsto (fun v => deriv (referenceEntranceStrongResponse k) v)
      (𝓝[<] 1) (𝓝 (k / Real.sqrt (k ^ 2 - 1))) := by
  apply (tendsto_referenceEntranceHeightResponse_one hk).congr'
  filter_upwards [(eventually_gt_nhds (zero_lt_one : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with v hv0 hv1
  exact (hasDerivAt_referenceEntranceStrongResponse_height hk ⟨hv0, hv1⟩).deriv.symm

end BianchiIX
