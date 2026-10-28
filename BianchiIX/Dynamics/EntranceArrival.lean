import BianchiIX.Dynamics.EntranceContinuation

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

theorem isClosed_normalized_entrance_times {x : NormalizedState} {t₀ s T k : ℝ}
    (hc : stateConstraint x = 1) (hk : 7 / 4 ≤ k) (hs : t₀ ≤ s) :
    IsClosed ({r | 1 / (2 * (k + 1) ^ 2) ≤ normalizedProjectiveRate x t₀ r ∧
      entranceRegion k (toProjectiveState (normalizedMaxCurve x t₀ r))} ∩ Icc s T) := by
  let a := normalizedProjectiveRate x t₀
  let Y := fun r => toProjectiveState (normalizedMaxCurve x t₀ r)
  let c := 1 / (2 * (k + 1) ^ 2)
  have hK : 0 < k + 1 := by linarith
  have hc0 : 0 < c := by dsimp [c]; positivity
  have hα (r : ℝ) (hr : r ∈ Icc s T) : ContinuousAt (normalizedMaxCurve x t₀) r :=
    (normalizedMaxCurve_forward_of_constraint hc (hs.trans hr.1)).1.continuousAt
  have ha : ContinuousOn a (Icc s T) := fun r hr =>
    (continuousAt_const.add ((continuous_apply 0).continuousAt.comp (hα r hr))).continuousWithinAt
  have hD : IsClosed (Icc s T ∩ {r | c ≤ a r}) :=
    ha.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have hY : ContinuousOn Y (Icc s T ∩ {r | c ≤ a r}) := by
    intro r hr
    exact ((contDiffAt_toProjectiveState 1 (hc0.trans_le hr.2).ne').continuousAt.comp (hα r hr.1)).continuousWithinAt
  have H := hY.preimage_isClosed_of_isClosed hD (isClosed_entranceRegion k)
  convert! H using 1
  ext r
  change (c ≤ a r ∧ entranceRegion k (Y r)) ∧ r ∈ Icc s T ↔
    (r ∈ Icc s T ∧ c ≤ a r) ∧ entranceRegion k (Y r)
  tauto

theorem exists_normalized_entrance_arrival {x : NormalizedState} {t₀ s k : ℝ}
    (hc : stateConstraint x = 1) (hk : 7 / 4 ≤ k) (hs : t₀ ≤ s)
    (hA : 0 < normalizedProjectiveRate x t₀ s) :
    let Y := fun r => toProjectiveState (normalizedMaxCurve x t₀ r)
    1 ≤ Y s 0 → coreRadius (Y s 0) (Y s 2) = k →
    (0 ≤ Y s 1 ∧ Y s 1 ≤ 1 / 10000) → (0 < Y s 2 ∧ Y s 2 < 1) →
    (0 ≤ Y s 3 ∧ Y s 3 ≤ 1 / 10000) →
    ∃ t > s, Y t 2 = 1 ∧ ∀ r ∈ Icc s t,
      1 / (2 * (k + 1) ^ 2) ≤ normalizedProjectiveRate x t₀ r ∧ entranceRegion k (Y r) := by
  intro Y hm hR hu hv hw
  have hk0 : 0 < k := by linarith
  have hK : 0 < k + 1 := by linarith
  let c := 1 / (2 * (k + 1) ^ 2)
  have hc0 : 0 < c := by dsimp [c]; positivity
  let S : Set ℝ := {r | c ≤ normalizedProjectiveRate x t₀ r ∧ entranceRegion k (Y r)}
  let T := s + (2 * (k + 1) ^ 2 / k) * Real.log (1 / Y s 2) + 1
  have hlog : 0 ≤ Real.log (1 / Y s 2) := by
    rw [one_div, Real.log_inv]
    exact neg_nonneg.mpr (Real.log_nonpos hv.1.le hv.2.le)
  have hsT : s ≤ T := by
    dsimp [T]
    nlinarith only [mul_nonneg (show 0 ≤ 2 * (k + 1) ^ 2 / k by positivity) hlog]
  have hRstrict : |coreRadius (Y s 0) (Y s 2) - k| < k / 100 := by rw [hR, sub_self, abs_zero]; positivity
  obtain ⟨r₀, hr₀, hprefix⟩ := normalized_entrance_local_prefix hc hk hs hA hm hRstrict hu hv hw
  have hsS : s ∈ S := ⟨(hprefix s ⟨le_rfl, hr₀.le⟩).1.le, (hprefix s ⟨le_rfl, hr₀.le⟩).2⟩
  have hdom (r : ℝ) (hr : s ≤ r) := normalizedMaxDomain_contains_Ici_of_constraint hc t₀ (hs.trans hr)
  have hpositive (r : ℝ) (hr : s ≤ r) (hAr : 0 < normalizedProjectiveRate x t₀ r) : 0 < Y r 2 :=
    normalized_projective_wall_pos (hdom s le_rfl) (hdom r hr) hA hAr 1 hv.1
  by_contra hnone
  have hwhole : Icc s T ⊆ S := by
    apply (isClosed_normalized_entrance_times hc hk hs).Icc_subset_of_forall_mem_nhdsGT_of_Icc_subset hsS
    intro t ht hbefore
    have htS := hbefore ⟨ht.1, le_rfl⟩
    have hAt : 0 < normalizedProjectiveRate x t₀ t := hc0.trans_le htS.1
    have hAbefore (r : ℝ) (hr : r ∈ Icc s t) : 0 < normalizedProjectiveRate x t₀ r := hc0.trans_le (hbefore hr).1
    have hstrict := (normalized_entrance_radius_improves hc hk hs ht.1 hAbefore
      (fun r hr => (hbefore hr).2) hv.1 hR).2
    have hvlt : Y t 2 < 1 := by
      rcases eq_or_lt_of_le ht.1 with heq | hst
      · subst t; exact hv.2
      · apply lt_of_le_of_ne htS.2.2.2.2.1.2
        intro heq
        exact hnone ⟨t, hst, heq, fun r hr => hbefore hr⟩
    obtain ⟨r, htr, hafter⟩ := normalized_entrance_local_prefix hc hk (hs.trans ht.1) hAt htS.2.1
      (hstrict.trans (by linarith)) htS.2.2.2.1 ⟨hpositive t ht.1 hAt, hvlt⟩ htS.2.2.2.2.2
    apply mem_nhdsGT_iff_exists_Ioc_subset.mpr
    exact ⟨r, htr, fun b hb => ⟨(hafter b ⟨hb.1.le, hb.2⟩).1.le, (hafter b ⟨hb.1.le, hb.2⟩).2⟩⟩
  have H := (normalized_entrance_residence hc hk hs hsT
    (fun r hr => hc0.trans_le (hwhole hr).1) (fun r hr => (hwhole hr).2) hv.1).2
  dsimp [T] at H
  linarith only [H]

theorem normalized_entrance_active_strictMono {x : NormalizedState} {t₀ s t k : ℝ}
    (hc : stateConstraint x = 1) (hk : 7 / 4 ≤ k) (hs : t₀ ≤ s) (hst : s ≤ t)
    (hA : ∀ r ∈ Icc s t, 0 < normalizedProjectiveRate x t₀ r) :
    let Y := fun r => toProjectiveState (normalizedMaxCurve x t₀ r)
    (∀ r ∈ Icc s t, entranceRegion k (Y r)) → 0 < Y s 2 →
    StrictMonoOn (fun r => Y r 2) (Icc s t) := by
  intro Y hy hvs
  have hdom (r : ℝ) (hr : s ≤ r) := normalizedMaxDomain_contains_Ici_of_constraint hc t₀ (hs.trans hr)
  have hv (r : ℝ) (hr : r ∈ Icc s t) : 0 < Y r 2 :=
    normalized_projective_wall_pos (hdom s le_rfl) (hdom r hr.1) (hA s ⟨le_rfl, hst⟩) (hA r hr) 1 hvs
  have hder (r : ℝ) (hr : r ∈ Icc s t) : HasDerivAt (fun b => Y b 2)
      (normalizedProjectiveRate x t₀ r * (entranceClockRate (Y r) * Y r 2)) r := by
    have H := normalizedMaxCurve_forward_of_constraint hc (hs.trans hr.1)
    exact hasDerivAt_pi.mp (hasDerivAt_toProjectiveState_normalized H.1 (hA r hr).ne' H.2.1) 2
  apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc s t) (HasDerivAt.continuousOn hder)
    (fun r hr => (hder r (interior_subset hr)).hasDerivWithinAt)
  intro r hr
  exact mul_pos (hA r (interior_subset hr))
    (mul_pos (entranceRegion_clock_pos hk (hy r (interior_subset hr))) (hv r (interior_subset hr)))

theorem exists_normalized_entrance_first_arrival {x : NormalizedState} {t₀ s k : ℝ}
    (hc : stateConstraint x = 1) (hk : 7 / 4 ≤ k) (hs : t₀ ≤ s)
    (hA : 0 < normalizedProjectiveRate x t₀ s) :
    let Y := fun r => toProjectiveState (normalizedMaxCurve x t₀ r)
    1 ≤ Y s 0 → coreRadius (Y s 0) (Y s 2) = k →
    (0 ≤ Y s 1 ∧ Y s 1 ≤ 1 / 10000) → (0 < Y s 2 ∧ Y s 2 < 1) →
    (0 ≤ Y s 3 ∧ Y s 3 ≤ 1 / 10000) →
    ∃ t > s, Y t 2 = 1 ∧ (∀ r ∈ Ico s t, Y r 2 < 1) ∧
      (∀ r ∈ Icc s t, 1 / (2 * (k + 1) ^ 2) ≤ normalizedProjectiveRate x t₀ r ∧ entranceRegion k (Y r)) ∧
      (∀ r ∈ Icc s t, |coreRadius (Y r 0) (Y r 2) - k| < k / 200 ∧
        Y r 1 ≤ Y s 1 * Real.exp (-(1 + k / 3) * (Real.log (Y r 2) - Real.log (Y s 2))) ∧
        Y r 3 ≤ Y s 3 * Real.exp (-(1 + 1 / k) * (Real.log (Y r 2) - Real.log (Y s 2)))) := by
  intro Y hm hR hu hv hw
  obtain ⟨t, hst, ht, hregion⟩ := exists_normalized_entrance_arrival hc hk hs hA hm hR hu hv hw
  have hK : 0 < k + 1 := by linarith
  have hpos : 0 < 1 / (2 * (k + 1) ^ 2) := by positivity
  have hAp (r : ℝ) (hr : r ∈ Icc s t) : 0 < normalizedProjectiveRate x t₀ r := hpos.trans_le (hregion r hr).1
  have hmono := normalized_entrance_active_strictMono hc hk hs hst.le hAp (fun r hr => (hregion r hr).2) hv.1
  refine ⟨t, hst, ht, ?_, hregion, ?_⟩
  · intro r hr
    rw [← ht]
    exact hmono ⟨hr.1, hr.2.le⟩ ⟨hst.le, le_rfl⟩ hr.2
  · intro r hr
    have hsub : Icc s r ⊆ Icc s t := fun b hb => ⟨hb.1, hb.2.trans hr.2⟩
    exact ⟨(normalized_entrance_radius_improves hc hk hs hr.1 (fun b hb => hAp b (hsub hb))
      (fun b hb => (hregion b (hsub hb)).2) hv.1 hR).2,
      normalized_entrance_decay hc hk hs hst.le hAp (fun b hb => (hregion b hb).2) hv.1 r hr⟩

end BianchiIX
