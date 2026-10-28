import BianchiIX.Dynamics.ExitClockInterval

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

/-- The terminal Einstein flight has one joint C2 clock family, including its initial endpoint. -/
theorem exists_terminal_exitClock_family {η : ℝ} (hη : 0 < η ∧ η < 1) {J : ℕ} (hJ : 1 ≤ J) :
    ∃ ε > (0 : ℝ), ∀ α b u w : ℝ,
      (0 < α ∧ α ≤ 1) → 0 < b → b ≤ ε * α ^ J → |u| + |w| ≤ b →
      let Y : ExitTailState := ![2 + 2 * α, u, w]
      let h := η * α ^ J
      let S := exitTailLength η α J
      coreTailValid h Y ∧ ∃ I : Set ℝ, IsOpen I ∧ Convex ℝ I ∧
        Icc 0 (coreTailTime h Y) ⊆ I ∧ ∃ U : Set ExitTailState, IsOpen U ∧ Y ∈ U ∧
        (∀ Z ∈ U, ∀ t ∈ I, exitEntryRegular Z t) ∧
        exitClockFlow I (Y, 0) = Y ∧
        ((fun Z => toExitTailState (coreTailState h Z)) =ᶠ[𝓝 Y] (fun Z => exitClockFlow I (Z, S))) ∧
        ∀ s ∈ Icc 0 S, ContDiffAt ℝ 2 (exitClockFlow I) (Y, s) ∧
          HasDerivAt (fun r => exitClockFlow I (Y, r))
            (exitTailField (Real.exp (-s)) (exitClockFlow I (Y, s))) s ∧
          ∀ v : ExitTailState,
            HasDerivAt (fun r => fderiv ℝ (exitClockFlow I) (Y, r) (v, 0))
              (fderiv ℝ (exitTailField (Real.exp (-s))) (exitClockFlow I (Y, s))
                (fderiv ℝ (exitClockFlow I) (Y, s) (v, 0))) s := by
  obtain ⟨A, _, ε, hε, HE⟩ := exists_terminal_coreTail_valid hη hJ
  refine ⟨ε, hε, ?_⟩
  intro α b u w hα hb hsmall hw Y h S
  obtain ⟨hvalid, hT, _, HP⟩ := HE α b u w hα hb hsmall hw
  change coreTailValid h Y at hvalid
  have hR : 1 < Y 0 := by change 1 < 2 + 2 * α; linarith only [hα.1]
  have hh : 0 < h := mul_pos hη.1 (pow_pos hα.1 J)
  have HR (t : ℝ) (ht : t ∈ Icc 0 (coreTailTime h Y)) : exitEntryRegular Y t := by
    have hphys := (HP t ht).2.1
    exact ⟨hR, coreTailValid_denom_pos hvalid, (hvalid.2.1 t ht).1, (hvalid.2.1 t ht).2,
      hh.trans_le hphys.2.2.2.1.1, lt_of_le_of_lt hphys.1 (by norm_num),
      lt_of_lt_of_le (by norm_num) (exitPhysicalRegion_clock hh hphys)⟩
  obtain ⟨U, hUo, hYU, l, r, hl, hr, H⟩ := exists_exitEntry_regular_tube hT.le HR
  have hcover : Icc 0 (coreTailTime h Y) ⊆ Ioo l r :=
    fun _ ht => ⟨hl.trans_le ht.1, ht.2.trans_lt hr⟩
  have h0 := hcover ⟨le_rfl, hT.le⟩
  have ht := hcover ⟨hT.le, le_rfl⟩
  have heh : -Real.log h = S := by
    change -Real.log (η * α ^ J) = exitTailLength η α J
    rw [← exp_neg_exitTailLength hη.1 hα.1 J, Real.log_exp, neg_neg]
  have hS : exitEntryClock (Y, coreTailTime h Y) = S := by
    change -Real.log (coreTailState h Y 2) = S
    rw [coreTailState_active hvalid]
    exact heh
  refine ⟨hvalid, Ioo l r, isOpen_Ioo, convex_Ioo l r, hcover, U, hUo, hYU, H,
    exitClockFlow_initial (convex_Ioo l r) (H Y hYU) h0, ?_, ?_⟩
  · simpa only [heh] using coreTailState_eventuallyEq_exitClockFlow isOpen_Ioo
      (convex_Ioo l r) hUo hYU H hvalid ht
  · intro s hs
    exact exitClockFlow_on_interval isOpen_Ioo (convex_Ioo l r) hUo hYU H hT.le hcover (hS ▸ hs)

end BianchiIX
