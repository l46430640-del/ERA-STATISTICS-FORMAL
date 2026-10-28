import BianchiIX.Dynamics.StableSecondCenterTail
import BianchiIX.Dynamics.StableProjectionFirstRegularity

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

def stableCenterSecondDifferential (c : ℝ) (y : StableState) (s : ℝ) :
    StableState →L[ℝ] (StableState →L[ℝ] ℝ) :=
  (ContinuousLinearMap.compL ℝ StableState StableState ℝ (ContinuousLinearMap.proj 0)).comp
    (stableRescaledSecondDifferential (c + 1) y s)

def stableCenterSecondDifferentialLimit (c : ℝ) (y : StableState) :
    StableState →L[ℝ] (StableState →L[ℝ] ℝ) :=
  limUnder atTop (stableCenterSecondDifferential c y)

theorem stableCenterSecondDifferential_apply (c : ℝ) (y : StableState) (s : ℝ)
    (v w : StableState) :
    stableCenterSecondDifferential c y s v w =
      stableRescaledSecondDifferential (c + 1) y s v w 0 := rfl

theorem hasFDerivAt_stableCenterDifferential {y : StableState} {c s : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 40)
    (hu : |y 1| ≤ 1 / 200) (hw : |y 2| ≤ 1 / 200) (hs : 0 ≤ s) :
    HasFDerivAt (fun z => stableCenterDifferential c z s)
      (stableCenterSecondDifferential c y s) y :=
  (ContinuousLinearMap.compL ℝ StableState StableState ℝ
    (ContinuousLinearMap.proj 0)).hasFDerivAt.comp y
      (hasFDerivAt_stableRescaledDifferential (by linarith : 0 < c + 1) hc hm hu hw hs)

theorem continuousOn_stableCenterSecondDifferential {c s : ℝ} (hc : 2 ≤ c) (hs : 0 ≤ s) :
    ContinuousOn (fun y => stableCenterSecondDifferential c y s) (stableParameterDomain c) := by
  intro y hy
  have hmap : ContinuousAt (fun z : StableState => (z, s)) y :=
    continuousAt_id.prodMk continuousAt_const
  have H := (continuousAt_stableRescaledSecondDifferential (by linarith : 0 < c + 1)
    hc hy.1.le hy.2.1.le hy.2.2.le hs).comp (f := fun z : StableState => (z, s)) hmap
  exact (continuousAt_const.clm_comp H).continuousWithinAt

theorem stableCenterSecondDifferential_tail {y : StableState} {c a t : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| < 1 / 40)
    (hu : |y 1| < 1 / 200) (hw : |y 2| < 1 / 200) (ha : 0 ≤ a) (hat : a ≤ t) :
    ‖stableCenterSecondDifferential c y t - stableCenterSecondDifferential c y a‖ ≤
      4 * stableSecondCenterBudget y * Real.exp (-a / 4) := by
  have hC := stableSecondCenterBudget_nonneg y
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro w
  change |stableRescaledSecondDifferential (c + 1) y t v w 0 -
    stableRescaledSecondDifferential (c + 1) y a v w 0| ≤ _
  convert! stableRescaledSecondDifferential_center_tail hc hm hu hw ha hat v w using 1
  ring

theorem stableSecondCenterBudget_decay (y : StableState) :
    Tendsto (fun t : ℝ => 4 * stableSecondCenterBudget y * Real.exp (-t / 4)) atTop (𝓝 0) := by
  have H := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
    (Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 4) tendsto_id)).const_mul
      (4 * stableSecondCenterBudget y)
  convert! H using 1
  · ext t
    simp only [Function.comp_def, id_eq]
    congr 2
    ring
  · simp

theorem stableCenterSecondDifferential_tendsto {y : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| < 1 / 40)
    (hu : |y 1| < 1 / 200) (hw : |y 2| < 1 / 200) :
    Tendsto (stableCenterSecondDifferential c y) atTop
      (𝓝 (stableCenterSecondDifferentialLimit c y)) := by
  have hC : CauchySeq (stableCenterSecondDifferential c y) := by
    apply (Metric.cauchySeq_iff' (u := stableCenterSecondDifferential c y)).mpr
    intro ε hε
    obtain ⟨R, hR⟩ := eventually_atTop.mp ((stableSecondCenterBudget_decay y).eventually (gt_mem_nhds hε))
    refine ⟨max R 0, fun t ht => ?_⟩
    rw [dist_eq_norm (stableCenterSecondDifferential c y t)
      (stableCenterSecondDifferential c y (max R 0))]
    exact (stableCenterSecondDifferential_tail hc hm hu hw (le_max_right _ _) ht).trans_lt
      (hR _ (le_max_left _ _))
  obtain ⟨L, hL⟩ := cauchy_map_iff_exists_tendsto.mp hC
  have heq : stableCenterSecondDifferentialLimit c y = L := hL.limUnder_eq
  rwa [heq]

theorem stableCenterSecondDifferentialLimit_tail {y : StableState} {c a : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| < 1 / 40)
    (hu : |y 1| < 1 / 200) (hw : |y 2| < 1 / 200) (ha : 0 ≤ a) :
    ‖stableCenterSecondDifferentialLimit c y - stableCenterSecondDifferential c y a‖ ≤
      4 * stableSecondCenterBudget y * Real.exp (-a / 4) := by
  let : ContinuousSub (StableState →L[ℝ] (StableState →L[ℝ] ℝ)) :=
    IsTopologicalAddGroup.to_continuousSub (G := StableState →L[ℝ] (StableState →L[ℝ] ℝ))
  have hlim : Tendsto (fun t : ℝ => stableCenterSecondDifferential c y t - stableCenterSecondDifferential c y a)
      atTop (𝓝 (stableCenterSecondDifferentialLimit c y - stableCenterSecondDifferential c y a)) :=
    (stableCenterSecondDifferential_tendsto hc hm hu hw).sub_const (stableCenterSecondDifferential c y a)
  have hnorm : Tendsto (fun t : ℝ => ‖stableCenterSecondDifferential c y t - stableCenterSecondDifferential c y a‖)
      atTop (𝓝 ‖stableCenterSecondDifferentialLimit c y - stableCenterSecondDifferential c y a‖) :=
    Tendsto.norm (E := StableState →L[ℝ] (StableState →L[ℝ] ℝ)) hlim
  apply le_of_tendsto hnorm
  filter_upwards [eventually_ge_atTop a] with t ht
  exact stableCenterSecondDifferential_tail hc hm hu hw ha ht

end BianchiIX
