import BianchiIX.Analysis.IntervalNeighborhood
import BianchiIX.Dynamics.ConnectionDrift
import BianchiIX.Dynamics.ConstrainedComplete

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

theorem exists_normalized_connection_regular_interval {x : NormalizedState} {t₀ s t : ℝ}
    (hst : s ≤ t) (hdom : Icc s t ⊆ normalizedMaxDomain x t₀)
    (hA : ∀ u ∈ Icc s t, 0 < 1 + normalizedMaxCurve x t₀ u 0)
    (hw : ∀ u ∈ Icc s t, 0 < toProjectiveState (normalizedMaxCurve x t₀ u) 3)
    (hD : ∀ u ∈ Icc s t, 0 < connectionClockRate (toProjectiveState (normalizedMaxCurve x t₀ u))) :
    ∃ l r : ℝ, l < s ∧ t < r ∧ ∀ u ∈ Ioo l r,
      u ∈ normalizedMaxDomain x t₀ ∧ 0 < 1 + normalizedMaxCurve x t₀ u 0 ∧
      0 < toProjectiveState (normalizedMaxCurve x t₀ u) 3 ∧
      0 < connectionClockRate (toProjectiveState (normalizedMaxCurve x t₀ u)) := by
  apply exists_Ioo_covering_of_eventually hst
  intro u hu
  have hα := (hasDerivAt_normalizedMaxCurve (hdom hu)).continuousAt
  have hAc : ContinuousAt (fun v => 1 + normalizedMaxCurve x t₀ v 0) u :=
    continuousAt_const.add ((continuous_apply 0).continuousAt.comp hα)
  have hβ : ContinuousAt (fun v => toProjectiveState (normalizedMaxCurve x t₀ v)) u :=
    (contDiffAt_toProjectiveState 1 (ne_of_gt (hA u hu))).continuousAt.comp hα
  have hwc := (continuous_apply (3 : Fin 4)).continuousAt.comp hβ
  have hDc := (contDiff_connectionClockRate 1).continuous.continuousAt.comp hβ
  have hmem : ∀ᶠ v in 𝓝 u, v ∈ normalizedMaxDomain x t₀ :=
    (isOpen_normalizedMaxDomain x t₀).mem_nhds (hdom hu)
  exact hmem.and ((hAc.eventually (isOpen_Ioi.mem_nhds (hA u hu))).and
    ((hwc.eventually (isOpen_Ioi.mem_nhds (hw u hu))).and
      (hDc.eventually (isOpen_Ioi.mem_nhds (hD u hu)))))

/-- The strict connection-band improvement applies to actual Einstein-flow prefixes. -/
theorem normalized_connection_phase_band_improves {x : NormalizedState} {t₀ s t μ : ℝ}
    (hc : stateConstraint x = 1) (hμ : 4 ≤ μ) (hs : t₀ ≤ s) (hst : s ≤ t)
    (hA : ∀ u ∈ Icc s t, 0 < 1 + normalizedMaxCurve x t₀ u 0) :
    let β := fun u => toProjectiveState (normalizedMaxCurve x t₀ u);
    -β s 0 = μ →
    (∀ u ∈ Icc s t, |-β u 0 - μ| ≤ 1 / 2) →
    (∀ u ∈ Icc s t, 0 ≤ β u 1 ∧ β u 1 ≤ 1 / 10000) →
    (∀ u ∈ Icc s t, 0 < β u 2 ∧ β u 2 ≤ 1) →
    (∀ u ∈ Icc s t, 0 < β u 3 ∧ β u 3 ≤ 1) → β s 1 ≤ β s 2 →
    |-β t 0 - μ| ≤ (3 / 2 + 12 * β s 1) / μ ∧ |-β t 0 - μ| < 1 / 2 := by
  intro β hinit hm hu hv hw hentry
  have hsm : s ∈ Icc s t := ⟨le_rfl, hst⟩
  have htm : t ∈ Icc s t := ⟨hst, le_rfl⟩
  have hdom : Icc s t ⊆ normalizedMaxDomain x t₀ := fun u hh =>
    normalizedMaxDomain_contains_Ici_of_constraint hc t₀ (hs.trans hh.1)
  have hD (u : ℝ) (hh : u ∈ Icc s t) : 0 < connectionClockRate (β u) := by
    have H := (connection_speed_bounds hμ (hm u hh) (hu u hh)
      ⟨(hv u hh).1.le, (hv u hh).2⟩ ⟨(hw u hh).1.le, (hw u hh).2⟩).1
    change μ / 2 ≤ connectionClockRate (β u) at H
    linarith only [H, hμ]
  obtain ⟨l, r, hls, htr, hregular⟩ := exists_normalized_connection_regular_interval hst hdom hA
    (fun u hh => (hw u hh).1) hD
  have hcover : Icc s t ⊆ Ioo l r := fun u hh => ⟨hls.trans_le hh.1, hh.2.trans_lt htr⟩
  have hsI := hcover hsm
  have htI := hcover htm
  obtain ⟨e, hsrc, heq, htarget, hzero, hinv0, hmono, hflow⟩ :=
    exists_normalized_connectionLog_reparametrization (convex_Ioo l r) isOpen_Ioo hsI
      (fun u hh => (hregular u hh).1) hc
      (fun u hh => (hregular u hh).2.1) (fun u hh => (hregular u hh).2.2.1)
      (fun u hh => (hregular u hh).2.2.2)
  have htE : t ∈ e.source := by rwa [hsrc]
  have hes : e s = 0 := by rw [heq s hsI]; exact sub_self _
  have hbt : 0 ≤ e t := by simpa only [hes] using hmono.monotoneOn hsI htI hst
  have hzt (z : ℝ) (hz : z ∈ Icc 0 (e t)) : z ∈ e.target :=
    htarget.ordConnected.out hzero (e.map_source htE) hz
  have hinv (z : ℝ) (hz : z ∈ Icc 0 (e t)) : e.symm z ∈ Icc s t := by
    have hzT := hzt z hz
    have hxI : e.symm z ∈ Ioo l r := by rw [← hsrc]; exact e.map_target hzT
    constructor
    · apply (hmono.le_iff_le hsI hxI).mp
      rw [hes, e.right_inv hzT]
      exact hz.1
    · apply (hmono.le_iff_le hxI htI).mp
      rw [e.right_inv hzT]
      exact hz.2
  let Y := fun z => β (e.symm z)
  have hY (z : ℝ) (hz : z ∈ Icc 0 (e t)) : HasDerivAt Y (connectionLogField (Y z)) z :=
    (hflow z (hzt z hz)).2.2
  have H := connectionLog_phase_band_improves hbt hμ hY
    (by change -β (e.symm 0) 0 = μ; rwa [hinv0])
    (fun z hz => hm _ (hinv z hz)) (fun z hz => hu _ (hinv z hz))
    (fun z hz => hv _ (hinv z hz))
    (fun z hz => ⟨(hw _ (hinv z hz)).1.le, (hw _ (hinv z hz)).2⟩)
    (by change β (e.symm 0) 1 ≤ β (e.symm 0) 2; rwa [hinv0])
  simpa only [Y, hinv0, e.left_inv htE] using H

end BianchiIX
