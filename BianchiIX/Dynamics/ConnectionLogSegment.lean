import BianchiIX.Dynamics.ConnectionRegion

noncomputable section

namespace BianchiIX

open Set

/-- The whole actual closed prefix is represented by one inverse logarithmic clock. -/
theorem exists_normalized_connection_log_segment {x : NormalizedState} {t₀ s t μ : ℝ}
    (hc : stateConstraint x = 1) (hμ : 4 ≤ μ) (hs : t₀ ≤ s) (hst : s ≤ t)
    (hA : ∀ u ∈ Icc s t, 0 < 1 + normalizedMaxCurve x t₀ u 0) :
    let β := fun u => toProjectiveState (normalizedMaxCurve x t₀ u)
    let L := Real.log (β t 3) - Real.log (β s 3)
    (∀ u ∈ Icc s t, connectionRegion μ (β u)) → 0 < β s 3 →
    0 ≤ L ∧ ∃ q : ℝ → ℝ, q 0 = s ∧ q L = t ∧ MapsTo q (Icc 0 L) (Icc s t) ∧
      (∀ u ∈ Icc s t, ∃ z ∈ Icc 0 L, q z = u) ∧
      (∀ z ∈ Icc 0 L, HasDerivAt (fun v => β (q v)) (connectionLogField (β (q z))) z) := by
  intro β L hregion hw
  have hsm : s ∈ Icc s t := ⟨le_rfl, hst⟩
  have htm : t ∈ Icc s t := ⟨hst, le_rfl⟩
  have hdom : Icc s t ⊆ normalizedMaxDomain x t₀ := fun u hu =>
    normalizedMaxDomain_contains_Ici_of_constraint hc t₀ (hs.trans hu.1)
  have hwpos (u : ℝ) (hu : u ∈ Icc s t) : 0 < β u 3 :=
    normalized_projective_wall_pos (hdom hsm) (hdom hu) (hA s hsm) (hA u hu) 2 hw
  have hD (u : ℝ) (hu : u ∈ Icc s t) : 0 < connectionClockRate (β u) := by
    have H := (connection_speed_bounds hμ (hregion u hu).1 (hregion u hu).2.1
      (hregion u hu).2.2.1 (hregion u hu).2.2.2).1
    change μ / 2 ≤ connectionClockRate (β u) at H
    linarith only [H, hμ]
  obtain ⟨l, r, hls, htr, hregular⟩ := exists_normalized_connection_regular_interval hst hdom hA hwpos hD
  have hcover : Icc s t ⊆ Ioo l r := fun u hu => ⟨hls.trans_le hu.1, hu.2.trans_lt htr⟩
  have hsI := hcover hsm
  have htI := hcover htm
  obtain ⟨e, hsrc, heq, htarget, hzero, hinv0, hmono, hflow⟩ :=
    exists_normalized_connectionLog_reparametrization (convex_Ioo l r) isOpen_Ioo hsI
      (fun u hu => (hregular u hu).1) hc (fun u hu => (hregular u hu).2.1)
      (fun u hu => (hregular u hu).2.2.1) (fun u hu => (hregular u hu).2.2.2)
  have hes : e s = 0 := by rw [heq s hsI]; exact sub_self _
  have het : e t = L := heq t htI
  have htE : t ∈ e.source := by rwa [hsrc]
  have hL : 0 ≤ L := by simpa only [hes, het] using hmono.monotoneOn hsI htI hst
  have hzt (z : ℝ) (hz : z ∈ Icc 0 L) : z ∈ e.target :=
    htarget.ordConnected.out hzero (het ▸ e.map_source htE) hz
  have hinv (z : ℝ) (hz : z ∈ Icc 0 L) : e.symm z ∈ Icc s t := by
    have hzT := hzt z hz
    have hxI : e.symm z ∈ Ioo l r := by rw [← hsrc]; exact e.map_target hzT
    constructor
    · apply (hmono.le_iff_le hsI hxI).mp
      rw [hes, e.right_inv hzT]
      exact hz.1
    · apply (hmono.le_iff_le hxI htI).mp
      rw [e.right_inv hzT, het]
      exact hz.2
  refine ⟨hL, e.symm, hinv0, ?_, hinv, ?_, fun z hz => (hflow z (hzt z hz)).2.2⟩
  · rw [← het]
    exact e.left_inv htE
  · intro u hu
    have huI := hcover hu
    refine ⟨e u, ⟨?_, ?_⟩, e.left_inv (by rwa [hsrc])⟩
    · simpa only [hes] using hmono.monotoneOn hsI huI hu.1
    · simpa only [het] using hmono.monotoneOn huI htI hu.2

end BianchiIX
