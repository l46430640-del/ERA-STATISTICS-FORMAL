import BianchiIX.Dynamics.ExitVariationClock
import BianchiIX.Dynamics.ExitTailArrival
import BianchiIX.Dynamics.CoreTailMultipliers

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

theorem toExitTailState_coreTailEntry {Y : ExitTailState} (hR : 1 < Y 0) :
    toExitTailState (coreTailEntry Y) = Y := by
  have HE := toExitTailState_fromExitTailState (Y := Y) (v := 1)
    (by linarith only [hR]) (by nlinarith only [hR])
  simpa only [coreTailEntry, fromExitTailState, exitTailGap, one_pow] using HE

theorem exitClockProjection_entry {Y : ExitTailState} (hR : 1 < Y 0) (v : ExitTailState) :
    exitClockProjection (coreTailEntry Y) (fderiv ℝ coreTailEntry Y v) = v := by
  have he := ((contDiffAt_coreTailEntry 1 hR).differentiableAt (by norm_num)).hasFDerivAt
  have hV : 0 < coreTailEntry Y 2 := by change (0 : ℝ) < 1; norm_num
  have hp := ((contDiffAt_toExitTailState 1 hV).differentiableAt (by norm_num)).hasFDerivAt
  have hc := ((contDiffAt_exitLogClock 1 hV).differentiableAt (by norm_num)).hasFDerivAt
  have hnear : (fun X => toExitTailState (coreTailEntry X)) =ᶠ[𝓝 Y] id := by
    filter_upwards [(continuous_apply 0).continuousAt.eventually (isOpen_Ioi.mem_nhds hR)] with X hX
    exact toExitTailState_coreTailEntry hX
  have HI := ((hp.comp Y he).congr_of_eventuallyEq hnear.symm).unique (hasFDerivAt_id Y)
  have hz : (fun X => exitLogClock (coreTailEntry X)) = fun _ : ExitTailState => (0 : ℝ) := by
    funext X
    simp [exitLogClock, coreTailEntry]
  have HZ := (hc.comp Y he).congr_of_eventuallyEq (Filter.Eventually.of_forall (congrFun hz.symm))
  have H0 := HZ.unique (hasFDerivAt_const (0 : ℝ) Y)
  have hI := congrArg (fun L : ExitTailState →L[ℝ] ExitTailState => L v) HI
  have h0 := congrArg (fun L : ExitTailState →L[ℝ] ℝ => L v) H0
  change fderiv ℝ exitLogClock (coreTailEntry Y) (fderiv ℝ coreTailEntry Y v) = 0 at h0
  change fderiv ℝ toExitTailState (coreTailEntry Y) (fderiv ℝ coreTailEntry Y v) = v at hI
  simpa only [exitClockProjection, h0, zero_smul, sub_zero] using hI

/-- A uniform bound for the actual Einstein tangent at fixed active-wall clock throughout the terminal flight. -/
theorem exists_terminal_exitProjected_bound {η : ℝ} (hη : 0 < η ∧ η < 1) {J : ℕ} (hJ : 1 ≤ J) :
    ∃ C ≥ (1 : ℝ), ∃ ε > (0 : ℝ), ∀ α b u w : ℝ,
      (0 < α ∧ α ≤ 1) → 0 < b → b ≤ ε * α ^ J → |u| + |w| ≤ b →
      let Y₀ : ExitTailState := ![2 + 2 * α, u, w]
      let y := coreTailEntry Y₀
      let h := η * α ^ J
      coreTailValid h Y₀ ∧
      ∀ t ∈ Icc 0 (coreTailTime h Y₀), ∀ v : ProjectiveState,
        ‖exitProjectedFlowVariation y 0 t v‖ ≤ C * ‖exitClockProjection y v‖ := by
  obtain ⟨C, hC, ε₁, hε₁, HV⟩ := exists_exitTail_uniform_linear_bound ⟨hη.1, hη.2.le⟩ hJ
  obtain ⟨A, hA, ε₂, hε₂, HE⟩ := exists_terminal_coreTail_valid hη hJ
  refine ⟨C, hC, min ε₁ ε₂, lt_min hε₁ hε₂, ?_⟩
  intro α b u w hα hb hsmall hw Y₀ y h
  have hb₁ := hsmall.trans (mul_le_mul_of_nonneg_right (min_le_left ε₁ ε₂) (pow_nonneg hα.1.le J))
  have hb₂ := hsmall.trans (mul_le_mul_of_nonneg_right (min_le_right ε₁ ε₂) (pow_nonneg hα.1.le J))
  obtain ⟨hvalid, hT, _, HP⟩ := HE α b u w hα hb hb₂ hw
  change coreTailValid h Y₀ at hvalid
  have hD : 0 < projectiveStateDenom y := coreTailValid_denom_pos hvalid
  let β := projectiveOriginalFlow y 0
  have hc : stateConstraint (fromProjectiveState y) = 1 := fromProjectiveState_constraint hD.ne'
  have hh : 0 < h := mul_pos hη.1 (pow_pos hα.1 J)
  have hβ0 : β 0 = y := projectiveOriginalFlow_initial hD 0
  have hV0 : β 0 2 = 1 := by rw [hβ0]; rfl
  have hY0 : toExitTailState (β 0) = Y₀ := by
    rw [hβ0]
    exact toExitTailState_coreTailEntry (by change 1 < 2 + 2 * α; linarith only [hα.1])
  refine ⟨hvalid, ?_⟩
  intro t ht v
  have hsub : Icc 0 t ⊆ Icc 0 (coreTailTime h Y₀) := fun _ hr => ⟨hr.1, hr.2.trans ht.2⟩
  have hdom : Icc 0 t ⊆ normalizedMaxDomain (fromProjectiveState y) 0 :=
    fun r hr => (hvalid.2.1 r (hsub hr)).1
  have hAf (r : ℝ) (hr : r ∈ Icc 0 t) :
      0 < 1 + normalizedMaxCurve (fromProjectiveState y) 0 r 0 := (hvalid.2.1 r (hsub hr)).2
  have hphys (r : ℝ) (hr : r ∈ Icc 0 t) : exitPhysicalRegion h (β r) := (HP r (hsub hr)).2.1
  have hVf (r : ℝ) (hr : r ∈ Icc 0 t) : 0 < β r 2 := hh.trans_le (hphys r hr).2.2.2.1.1
  have hMf (r : ℝ) (hr : r ∈ Icc 0 t) : β r 0 < 1 :=
    lt_of_le_of_lt (hphys r hr).1 (by norm_num)
  have hdf (r : ℝ) (hr : r ∈ Icc 0 t) : 0 < exitClockRate (β r) :=
    lt_of_lt_of_le (by norm_num) (exitPhysicalRegion_clock hh (hphys r hr))
  obtain ⟨l, r, hl, hr, hregular⟩ := exists_normalized_exit_regular_interval ht.1 hdom hAf hVf hMf hdf
  have hcover : Icc 0 t ⊆ Ioo l r := fun _ hz => ⟨hl.trans_le hz.1, hz.2.trans_lt hr⟩
  have h0I := hcover ⟨le_rfl, ht.1⟩
  have htI := hcover ⟨ht.1, le_rfl⟩
  obtain ⟨e, hsrc, heq, htarget, hzero, hinv0, hmono, hflow⟩ :=
    exists_normalized_exitLog_reparametrization (convex_Ioo l r) isOpen_Ioo h0I
      (fun z hz => (hregular z hz).1) hc (fun z hz => (hregular z hz).2.1)
      (fun z hz => (hregular z hz).2.2.1) (fun z hz => (hregular z hz).2.2.2.2)
  have htE : t ∈ e.source := by rwa [hsrc]
  have he0 : e 0 = 0 := by rw [heq 0 h0I]; exact sub_self _
  have het : e t = -Real.log (β t 2) := by
    rw [heq t htI]
    change Real.log (β 0 2) - Real.log (β t 2) = _
    rw [hV0, Real.log_one, zero_sub]
  have hEt : 0 ≤ e t := by simpa only [he0] using hmono.monotoneOn h0I htI ht.1
  have hEL : e t ≤ exitTailLength η α J := by
    have H := Real.log_le_log hh (hphys t ⟨ht.1, le_rfl⟩).2.2.2.1.1
    change Real.log (η * α ^ J) ≤ Real.log (β t 2) at H
    rw [← exp_neg_exitTailLength hη.1 hα.1 J, Real.log_exp] at H
    rw [het]
    linarith only [H]
  have hzt (z : ℝ) (hz : z ∈ Icc 0 (e t)) : z ∈ e.target :=
    htarget.ordConnected.out hzero (e.map_source htE) hz
  have hinv (z : ℝ) (hz : z ∈ Icc 0 (e t)) : e.symm z ∈ Icc 0 t := by
    have hzT := hzt z hz
    have hxI : e.symm z ∈ Ioo l r := by rw [← hsrc]; exact e.map_target hzT
    constructor
    · apply (hmono.le_iff_le h0I hxI).mp
      rw [he0, e.right_inv hzT]
      exact hz.1
    · apply (hmono.le_iff_le hxI htI).mp
      rw [e.right_inv hzT]
      exact hz.2
  let Y : ℝ → ExitTailState := fun z => toExitTailState (β (e.symm z))
  have hval (z : ℝ) (hz : z ∈ Icc 0 (e t)) : β (e.symm z) 2 = Real.exp (-z) := by
    have H := (hflow z (hzt z hz)).2.1
    change β (e.symm z) 2 = β 0 2 * Real.exp (-z) at H
    simpa only [hV0, one_mul] using H
  have hY (z : ℝ) (hz : z ∈ Icc 0 (e t)) : HasDerivAt Y (exitTailField (Real.exp (-z)) (Y z)) z := by
    have H := hasDerivAt_toExitTailState (hflow z (hzt z hz)).2.2
      (hVf _ (hinv z hz)) (hMf _ (hinv z hz))
    change HasDerivAt Y (exitTailField (β (e.symm z) 2) (Y z)) z at H
    rwa [hval z hz] at H
  have HY0 : Y 0 = Y₀ := by dsimp only [Y]; rw [hinv0]; exact hY0
  let X := fun z => exitProjectedFlowVariation y 0 (e.symm z) v
  have hX (z : ℝ) (hz : z ∈ Icc 0 (e t)) : HasDerivAt X
      (fderiv ℝ (exitTailField (Real.exp (-z))) (Y z) (X z)) z := by
    have hz' := hinv z hz
    have hτ : HasDerivAt e.symm (1 / exitOriginalClockRate (β (e.symm z))) z := by
      rw [exitOriginalClockRate_normalized hD (hdom hz') (hAf _ hz')]
      exact (hflow z (hzt z hz)).1
    have H := hasDerivAt_exitProjectedFlowVariation_clock hD (hdom hz') (hAf _ hz')
      (hVf _ hz') (hMf _ hz') (hdf _ hz').ne' hτ v
    change HasDerivAt X (fderiv ℝ (exitTailField (β (e.symm z) 2)) (Y z) (X z)) z at H
    rwa [hval z hz] at H
  have H := HV α b (e t) Y hα hb hb₁ ⟨hEt, hEL⟩
    (by rw [HY0]; rfl) (by rw [HY0]; exact hw) hY X 0 (e t) le_rfl hEt le_rfl hX
  simpa only [X, e.left_inv htE, hinv0, exitProjectedFlowVariation_initial hD] using H

theorem exists_terminal_exitProjected_entry_bound {η : ℝ} (hη : 0 < η ∧ η < 1) {J : ℕ} (hJ : 1 ≤ J) :
    ∃ C ≥ (1 : ℝ), ∃ ε > (0 : ℝ), ∀ α b u w : ℝ,
      (0 < α ∧ α ≤ 1) → 0 < b → b ≤ ε * α ^ J → |u| + |w| ≤ b →
      let Y₀ : ExitTailState := ![2 + 2 * α, u, w]
      coreTailValid (η * α ^ J) Y₀ ∧
      ∀ t ∈ Icc 0 (coreTailTime (η * α ^ J) Y₀), ∀ v : ExitTailState,
        ‖exitProjectedFlowVariation (coreTailEntry Y₀) 0 t (fderiv ℝ coreTailEntry Y₀ v)‖ ≤ C * ‖v‖ := by
  obtain ⟨C, hC, ε, hε, H⟩ := exists_terminal_exitProjected_bound hη hJ
  refine ⟨C, hC, ε, hε, ?_⟩
  intro α b u w hα hb hsmall hw Y₀
  have HP := H α b u w hα hb hsmall hw
  refine ⟨HP.1, ?_⟩
  intro t ht v
  have HB := HP.2 t ht (fderiv ℝ coreTailEntry Y₀ v)
  change ‖exitProjectedFlowVariation (coreTailEntry Y₀) 0 t (fderiv ℝ coreTailEntry Y₀ v)‖ ≤
    C * ‖exitClockProjection (coreTailEntry Y₀) (fderiv ℝ coreTailEntry Y₀ v)‖ at HB
  rwa [exitClockProjection_entry (show 1 < Y₀ 0 by change 1 < 2 + 2 * α; linarith only [hα.1])] at HB

end BianchiIX
