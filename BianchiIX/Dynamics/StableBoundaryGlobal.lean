import BianchiIX.Dynamics.StableBoundaryPrefix
import BianchiIX.Dynamics.CoreEntry
import Mathlib.Topology.Order.IntermediateValue

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

theorem isClosed_normalized_stable_times {x : NormalizedState} {t₀ s T c : ℝ}
    (hx : stateConstraint x = 1) (hc : 2 ≤ c) (hs : t₀ ≤ s) :
    IsClosed ({r | 3 / (2 * (c + 1) ^ 2) ≤ normalizedProjectiveRate x t₀ r ∧
      stableBoundaryRegion c (toProjectiveState (normalizedMaxCurve x t₀ r))} ∩ Icc s T) := by
  let A := normalizedProjectiveRate x t₀
  let Y := fun r => toProjectiveState (normalizedMaxCurve x t₀ r)
  let d := 3 / (2 * (c + 1) ^ 2)
  have hd : 0 < d := by
    dsimp [d]
    have : 0 < c + 1 := by linarith
    positivity
  have hα (r : ℝ) (hr : r ∈ Icc s T) :=
    (normalizedMaxCurve_forward_of_constraint hx (hs.trans hr.1)).1.continuousAt
  have hAc : ContinuousOn A (Icc s T) := fun r hr =>
    (continuousAt_const.add ((continuous_apply 0).continuousAt.comp (hα r hr))).continuousWithinAt
  have hD : IsClosed (Icc s T ∩ {r | d ≤ A r}) :=
    hAc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have hY : ContinuousOn Y (Icc s T ∩ {r | d ≤ A r}) := by
    intro r hr
    exact ((contDiffAt_toProjectiveState 1 (ne_of_gt (hd.trans_le hr.2))).continuousAt.comp
      (hα r hr.1)).continuousWithinAt
  have H := hY.preimage_isClosed_of_isClosed hD (isClosed_stableBoundaryRegion c)
  convert! H using 1
  ext r
  change (d ≤ A r ∧ stableBoundaryRegion c (Y r)) ∧ r ∈ Icc s T ↔
    (r ∈ Icc s T ∧ d ≤ A r) ∧ stableBoundaryRegion c (Y r)
  tauto

theorem normalized_stable_local_prefix {x : NormalizedState} {t₀ s c : ℝ}
    (hx : stateConstraint x = 1) (hc : 2 ≤ c) (hs : t₀ ≤ s)
    (hA : 0 < normalizedProjectiveRate x t₀ s) :
    let Y := fun r => toProjectiveState (normalizedMaxCurve x t₀ r)
    |Y s 0 - c| < 1 / 10 → |Y s 1| < 1 / 100 → Y s 2 = 0 → |Y s 3| < 1 / 100 →
    ∃ T > s, ∀ r ∈ Icc s T,
      3 / (2 * (c + 1) ^ 2) < normalizedProjectiveRate x t₀ r ∧ stableBoundaryRegion c (Y r) := by
  intro Y hm hu hv hw
  have hactual := normalizedMaxCurve_forward_of_constraint hx hs
  have hsol : HasDerivAt Y (normalizedProjectiveRate x t₀ s • projectiveField (Y s)) s :=
    hasDerivAt_toProjectiveState_normalized hactual.1 (ne_of_gt hA) hactual.2.1
  have hcoord (i : Fin 4) := (hasDerivAt_pi.mp hsol i).continuousAt
  have hAc : ContinuousAt (normalizedProjectiveRate x t₀) s :=
    continuousAt_const.add (hasDerivAt_pi.mp hactual.1 0).continuousAt
  have hK : 0 < c + 1 := by linarith
  have hmargin : 3 / (2 * (c + 1) ^ 2) < normalizedProjectiveRate x t₀ s := by
    apply lt_of_lt_of_le _ (normalized_stable_chart_lower hc (ne_of_gt hA) hactual.2.1
      ⟨hm.le, hu.le, hv, hw.le⟩)
    apply (div_lt_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith only [sq_pos_of_pos hK]
  have H : ∀ᶠ r in 𝓝[>] s,
      3 / (2 * (c + 1) ^ 2) < normalizedProjectiveRate x t₀ r ∧
      |Y r 0 - c| < 1 / 10 ∧ |Y r 1| < 1 / 100 ∧ |Y r 3| < 1 / 100 := by
    filter_upwards [(hAc.eventually (isOpen_Ioi.mem_nhds hmargin)).filter_mono nhdsWithin_le_nhds,
      (((hcoord 0).sub continuousAt_const).abs.eventually (isOpen_Iio.mem_nhds hm)).filter_mono nhdsWithin_le_nhds,
      ((hcoord 1).abs.eventually (isOpen_Iio.mem_nhds hu)).filter_mono nhdsWithin_le_nhds,
      ((hcoord 3).abs.eventually (isOpen_Iio.mem_nhds hw)).filter_mono nhdsWithin_le_nhds]
      with r hr hm hu hw
    exact ⟨hr, hm, hu, hw⟩
  obtain ⟨T, hT, hsub⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp H
  refine ⟨T, hT, ?_⟩
  intro r hr
  rcases eq_or_lt_of_le hr.1 with heq | hlt
  · subst r
    exact ⟨hmargin, hm.le, hu.le, hv, hw.le⟩
  have H := hsub ⟨hlt, hr.2⟩
  have hAr : 0 < normalizedProjectiveRate x t₀ r :=
    lt_trans (by positivity : 0 < 3 / (2 * (c + 1) ^ 2)) H.1
  have hVr := (normalized_projective_wall_sign
    (normalizedMaxDomain_contains_Ici_of_constraint hx t₀ hs)
    (normalizedMaxDomain_contains_Ici_of_constraint hx t₀ (hs.trans hlt.le)) hA hAr 1).1.mpr hv
  exact ⟨H.1, H.2.1.le, H.2.2.1.le, hVr, H.2.2.2.le⟩

/-- The actual signed boundary flow stays in one fixed chart for all future time. -/
theorem normalized_stable_global_region {x : NormalizedState} {t₀ s c : ℝ}
    (hx : stateConstraint x = 1) (hc : 2 ≤ c) (hs : t₀ ≤ s)
    (hA : 0 < normalizedProjectiveRate x t₀ s) :
    let Y := fun r => toProjectiveState (normalizedMaxCurve x t₀ r)
    |Y s 0 - c| ≤ 1 / 40 → |Y s 1| ≤ 1 / 200 → Y s 2 = 0 → |Y s 3| ≤ 1 / 200 →
    ∀ r ≥ s, 3 / (c + 1) ^ 2 ≤ normalizedProjectiveRate x t₀ r ∧
      stableBoundaryRegion c (Y r) ∧
      |Y r 0 - Y s 0| ≤ 8 * (|Y s 1| + |Y s 3|) ^ 2 / (c + 1) ∧
      |Y r 1| ≤ |Y s 1| ∧ |Y r 3| ≤ |Y s 3| := by
  intro Y hm hu hv hw T hT
  let d := 3 / (2 * (c + 1) ^ 2)
  have hK : 0 < c + 1 := by linarith
  have hd : 0 < d := by dsimp [d]; positivity
  let S := {r | d ≤ normalizedProjectiveRate x t₀ r ∧ stableBoundaryRegion c (Y r)}
  obtain ⟨r₀, hr₀, hprefix⟩ := normalized_stable_local_prefix hx hc hs hA
    (by linarith : |Y s 0 - c| < 1 / 10) (by linarith : |Y s 1| < 1 / 100)
    hv (by linarith : |Y s 3| < 1 / 100)
  have hsS : s ∈ S := ⟨(hprefix s ⟨le_rfl, hr₀.le⟩).1.le, (hprefix s ⟨le_rfl, hr₀.le⟩).2⟩
  have hbudget : 8 * (|Y s 1| + |Y s 3|) ^ 2 / (c + 1) < 1 / 40 := by
    apply (div_lt_iff₀ hK).mpr
    have hb0 : 0 ≤ |Y s 1| + |Y s 3| := by positivity
    have hb : |Y s 1| + |Y s 3| ≤ 1 / 100 := by linarith
    have hb2 := (sq_le_sq₀ hb0 (by norm_num : (0 : ℝ) ≤ 1 / 100)).mpr hb
    nlinarith
  have hwhole : Icc s T ⊆ S := by
    apply (isClosed_normalized_stable_times hx hc hs).Icc_subset_of_forall_mem_nhdsGT_of_Icc_subset hsS
    intro t ht hbefore
    have htS := hbefore ⟨ht.1, le_rfl⟩
    have hAt : 0 < normalizedProjectiveRate x t₀ t := hd.trans_le htS.1
    have H := normalized_stable_prefix_estimates hx hc hs ht.1
      (fun r hr => hd.trans_le (hbefore hr).1) (fun r hr => (hbefore hr).2)
    have hMt : |Y t 0 - c| < 1 / 10 := by
      have htri : |Y t 0 - c| ≤ |Y t 0 - Y s 0| + |Y s 0 - c| := by
        exact abs_sub_le (Y t 0) (Y s 0) c
      have hsmall := H.1.trans_lt hbudget
      linarith
    have hU := (H.2.2 t ⟨ht.1, le_rfl⟩).1.trans hu
    have hW := (H.2.2 t ⟨ht.1, le_rfl⟩).2.trans hw
    obtain ⟨r, htr, hafter⟩ := normalized_stable_local_prefix hx hc (hs.trans ht.1) hAt hMt
      (by linarith : |Y t 1| < 1 / 100) htS.2.2.2.1 (by linarith : |Y t 3| < 1 / 100)
    apply mem_nhdsGT_iff_exists_Ioc_subset.mpr
    exact ⟨r, htr, fun q hq => ⟨(hafter q ⟨hq.1.le, hq.2⟩).1.le, (hafter q ⟨hq.1.le, hq.2⟩).2⟩⟩
  have htS := hwhole ⟨hT, le_rfl⟩
  have H := normalized_stable_prefix_estimates hx hc hs hT
    (fun r hr => hd.trans_le (hwhole hr).1) (fun r hr => (hwhole hr).2)
  exact ⟨normalized_stable_chart_lower hc (ne_of_gt (hd.trans_le htS.1))
      (normalizedMaxCurve_forward_of_constraint hx (hs.trans hT)).2.1 htS.2,
    htS.2, H.1, H.2.2 T ⟨hT, le_rfl⟩⟩

end BianchiIX
