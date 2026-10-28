import BianchiIX.Dynamics.ConnectionArrivalVariation

noncomputable section

namespace BianchiIX

open Set

/-- The full canonical first return supplies every geometric and clock hypothesis of the variation estimates. -/
theorem exists_connectionReturn_log_clock {p : ConnectionParameters} (hμ : 4 ≤ p 0)
    (hu : 0 < p 1 ∧ p 1 ≤ (1 / 10000) / p 0) (hw : 0 < p 2 ∧ p 2 ≤ 1 / 10000) :
    let y := connectionEntry (p 0) (p 1) (p 2)
    let L := -Real.log (p 2)
    0 ≤ L ∧ ∃ q : ℝ → ℝ, q 0 = 0 ∧ q L = connectionReturnTime p ∧
      ∀ z ∈ Icc 0 L,
        q z ∈ normalizedMaxDomain (fromProjectiveState y) 0 ∧
        0 < 1 + normalizedMaxCurve (fromProjectiveState y) 0 (q z) 0 ∧
        connectionRegion (p 0) (projectiveOriginalFlow y 0 (q z)) ∧
        0 < projectiveOriginalFlow y 0 (q z) 1 ∧
        0 < projectiveOriginalFlow y 0 (q z) 2 ∧
        0 < projectiveOriginalFlow y 0 (q z) 3 ∧
        HasDerivAt q (1 / connectionOriginalClockRate (projectiveOriginalFlow y 0 (q z))) z := by
  intro y L
  let T := connectionReturnTime p
  let β : ℝ → ProjectiveState := projectiveOriginalFlow y 0
  have hu' : 0 ≤ p 1 ∧ p 1 ≤ (1 / 10000) / p 0 := ⟨hu.1.le, hu.2⟩
  have hden := connection_entry_denom_pos hμ hu' hw
  have hc : stateConstraint (fromProjectiveState y) = 1 := fromProjectiveState_constraint (ne_of_gt hden)
  have hvalid := (connectionReturn_regular hμ hu' hw).1
  have hcontrol := connectionReturn_control hμ hu' hw
  have hT : 0 < T := hcontrol.1
  have hdom (t : ℝ) (ht : t ∈ Icc 0 T) : t ∈ normalizedMaxDomain (fromProjectiveState y) 0 := (hvalid.2.1 t ht).1
  have hA (t : ℝ) (ht : t ∈ Icc 0 T) : 0 < 1 + normalizedMaxCurve (fromProjectiveState y) 0 t 0 := (hvalid.2.1 t ht).2
  have hregion (t : ℝ) (ht : t ∈ Icc 0 T) : connectionRegion (p 0) (β t) := (hcontrol.2 t ht).2
  have hinit : β 0 = y := projectiveOriginalFlow_initial hden 0
  have hentry (i : Fin 3) : 0 < β 0 i.succ := by
    rw [hinit]
    fin_cases i
    · exact hu.1
    · change (0 : ℝ) < 1
      norm_num
    · exact hw.1
  have hpos (t : ℝ) (ht : t ∈ Icc 0 T) (i : Fin 3) : 0 < β t i.succ :=
    normalized_projective_wall_pos (hdom 0 ⟨le_rfl, hT.le⟩) (hdom t ht)
      (hA 0 ⟨le_rfl, hT.le⟩) (hA t ht) i (hentry i)
  have hD (t : ℝ) (ht : t ∈ Icc 0 T) : 0 < connectionClockRate (β t) := by
    have H := (connection_speed_bounds hμ (hregion t ht).1 (hregion t ht).2.1
      (hregion t ht).2.2.1 (hregion t ht).2.2.2).1
    change p 0 / 2 ≤ connectionClockRate (β t) at H
    linarith only [H, hμ]
  obtain ⟨l, r, hl, hr, hregular⟩ := exists_normalized_connection_regular_interval hT.le hdom hA
    (fun t ht => hpos t ht 2) hD
  have hcover : Icc 0 T ⊆ Ioo l r := fun t ht => ⟨hl.trans_le ht.1, ht.2.trans_lt hr⟩
  have h0I := hcover ⟨le_rfl, hT.le⟩
  have hTI := hcover ⟨hT.le, le_rfl⟩
  obtain ⟨e, hsrc, heq, htarget, hzero, hinv0, hmono, hflow⟩ :=
    exists_normalized_connectionLog_reparametrization (convex_Ioo l r) isOpen_Ioo h0I
      (fun t ht => (hregular t ht).1) hc (fun t ht => (hregular t ht).2.1)
      (fun t ht => (hregular t ht).2.2.1) (fun t ht => (hregular t ht).2.2.2)
  have he0 : e 0 = 0 := by rw [heq 0 h0I]; exact sub_self _
  have hWend : β T 3 = 1 := (connectionReturn_growing_component hμ hu' hw).1
  have heT : e T = L := by
    rw [heq T hTI]
    change Real.log (β T 3) - Real.log (β 0 3) = L
    rw [hWend, hinit]
    simp [L, y, connectionEntry]
  have hTE : T ∈ e.source := by rwa [hsrc]
  have hL : 0 ≤ L := by simpa only [he0, heT] using hmono.monotoneOn h0I hTI hT.le
  have hzt (z : ℝ) (hz : z ∈ Icc 0 L) : z ∈ e.target :=
    htarget.ordConnected.out hzero (heT ▸ e.map_source hTE) hz
  have hinv (z : ℝ) (hz : z ∈ Icc 0 L) : e.symm z ∈ Icc 0 T := by
    have hxI : e.symm z ∈ Ioo l r := by rw [← hsrc]; exact e.map_target (hzt z hz)
    constructor
    · apply (hmono.le_iff_le h0I hxI).mp
      rw [he0, e.right_inv (hzt z hz)]
      exact hz.1
    · apply (hmono.le_iff_le hxI hTI).mp
      rw [e.right_inv (hzt z hz), heT]
      exact hz.2
  refine ⟨hL, e.symm, hinv0, ?_, ?_⟩
  · rw [← heT]
    exact e.left_inv hTE
  · intro z hz
    have ht := hinv z hz
    refine ⟨hdom _ ht, hA _ ht, hregion _ ht, hpos _ ht 0, hpos _ ht 1, hpos _ ht 2, ?_⟩
    have hc' := (normalizedMaxCurve_constraint (hdom _ ht)).trans hc
    have hscale := projective_inverse_scale (ne_of_gt (hA _ ht)) hc'
    change 6 / projectiveStateDenom (β (e.symm z)) = 1 + normalizedMaxCurve (fromProjectiveState y) 0 (e.symm z) 0 at hscale
    change HasDerivAt e.symm (1 / connectionOriginalClockRate (β (e.symm z))) z
    rw [connectionOriginalClockRate, hscale]
    exact (hflow z (hzt z hz)).1

end BianchiIX
