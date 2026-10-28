import BianchiIX.Dynamics.ExitPhysicalRegion
import BianchiIX.Analysis.IntervalNeighborhood

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

theorem exists_normalized_exit_regular_interval {x : NormalizedState} {t₀ s t : ℝ}
    (hst : s ≤ t) (hdom : Icc s t ⊆ normalizedMaxDomain x t₀)
    (hA : ∀ u ∈ Icc s t, 0 < 1 + normalizedMaxCurve x t₀ u 0)
    (hv : ∀ u ∈ Icc s t, 0 < toProjectiveState (normalizedMaxCurve x t₀ u) 2)
    (hM : ∀ u ∈ Icc s t, toProjectiveState (normalizedMaxCurve x t₀ u) 0 < 1)
    (hD : ∀ u ∈ Icc s t, 0 < exitClockRate (toProjectiveState (normalizedMaxCurve x t₀ u))) :
    ∃ l r : ℝ, l < s ∧ t < r ∧ ∀ u ∈ Ioo l r,
      u ∈ normalizedMaxDomain x t₀ ∧ 0 < 1 + normalizedMaxCurve x t₀ u 0 ∧
      0 < toProjectiveState (normalizedMaxCurve x t₀ u) 2 ∧
      toProjectiveState (normalizedMaxCurve x t₀ u) 0 < 1 ∧
      0 < exitClockRate (toProjectiveState (normalizedMaxCurve x t₀ u)) := by
  apply exists_Ioo_covering_of_eventually hst
  intro u hu
  have hα := (hasDerivAt_normalizedMaxCurve (hdom hu)).continuousAt
  have hAc : ContinuousAt (fun v => 1 + normalizedMaxCurve x t₀ v 0) u :=
    continuousAt_const.add ((continuous_apply 0).continuousAt.comp hα)
  have hβ : ContinuousAt (fun v => toProjectiveState (normalizedMaxCurve x t₀ v)) u :=
    (contDiffAt_toProjectiveState 1 (ne_of_gt (hA u hu))).continuousAt.comp hα
  have hvc := (continuous_apply (2 : Fin 4)).continuousAt.comp hβ
  have hmc := (continuous_apply (0 : Fin 4)).continuousAt.comp hβ
  have hDc := (contDiff_exitClockRate 1).continuous.continuousAt.comp hβ
  have hmem : ∀ᶠ v in 𝓝 u, v ∈ normalizedMaxDomain x t₀ :=
    (isOpen_normalizedMaxDomain x t₀).mem_nhds (hdom hu)
  exact hmem.and ((hAc.eventually (isOpen_Ioi.mem_nhds (hA u hu))).and
    ((hvc.eventually (isOpen_Ioi.mem_nhds (hv u hu))).and
      ((hmc.eventually (isOpen_Iio.mem_nhds (hM u hu))).and
        (hDc.eventually (isOpen_Ioi.mem_nhds (hD u hu))))))

/-- Uniform signed tail estimates applied to actual normalized-flow prefixes. -/
theorem exists_normalized_exit_prefix_bounds {η : ℝ} (hη : 0 < η ∧ η ≤ 1) {J : ℕ} (hJ : 1 ≤ J) :
    ∃ A ≥ (2 : ℝ), ∃ ε > (0 : ℝ), ∀ (x : NormalizedState) (t₀ s t α b : ℝ),
      stateConstraint x = 1 → t₀ ≤ s → s ≤ t → (0 < α ∧ α ≤ 1) →
      0 < b → b ≤ ε * α ^ J →
      (∀ u ∈ Icc s t, 0 < 1 + normalizedMaxCurve x t₀ u 0) →
      let β := fun u => toProjectiveState (normalizedMaxCurve x t₀ u)
      (∀ u ∈ Icc s t, exitPhysicalRegion (η * α ^ J) (β u)) → β s 2 = 1 →
      coreRadius (β s 0) (β s 2) = 2 + 2 * α → |β s 1| + |β s 3| ≤ b →
      |β t 1| + |β t 3| ≤ A * b / 2 ∧
      |coreRadius (β t 0) (β t 2) - coreRadius (β s 0) (β s 2)| ≤ 40 * A * b ∧
      2 + α < coreRadius (β t 0) (β t 2) ∧ |β t 1| ≤ β t 2 / 2 := by
  obtain ⟨A, hA, ε, hε, HP⟩ := exists_exitTail_scale_bounds hη hJ
  refine ⟨A, hA, ε, hε, ?_⟩
  intro x t₀ s t α b hc hs hst hα hb hsmall hAflow β hregion hV hR hw
  have hh : 0 < η * α ^ J := mul_pos hη.1 (pow_pos hα.1 J)
  have hsm : s ∈ Icc s t := ⟨le_rfl, hst⟩
  have htm : t ∈ Icc s t := ⟨hst, le_rfl⟩
  have hdom : Icc s t ⊆ normalizedMaxDomain x t₀ := fun u hu =>
    normalizedMaxDomain_contains_Ici_of_constraint hc t₀ (hs.trans hu.1)
  have hv (u : ℝ) (hu : u ∈ Icc s t) : 0 < β u 2 := hh.trans_le (hregion u hu).2.2.2.1.1
  have hm (u : ℝ) (hu : u ∈ Icc s t) : β u 0 < 1 := lt_of_le_of_lt (hregion u hu).1 (by norm_num)
  have hd (u : ℝ) (hu : u ∈ Icc s t) : 0 < exitClockRate (β u) := by
    have H := exitPhysicalRegion_clock hh (hregion u hu)
    linarith only [H]
  obtain ⟨l, r, hls, htr, hregular⟩ := exists_normalized_exit_regular_interval hst hdom hAflow hv hm hd
  have hcover : Icc s t ⊆ Ioo l r := fun u hu => ⟨hls.trans_le hu.1, hu.2.trans_lt htr⟩
  have hsI := hcover hsm
  have htI := hcover htm
  obtain ⟨e, hsrc, heq, htarget, hzero, hinv0, hmono, hflow⟩ :=
    exists_normalized_exitLog_reparametrization (convex_Ioo l r) isOpen_Ioo hsI
      (fun u hu => (hregular u hu).1) hc (fun u hu => (hregular u hu).2.1)
      (fun u hu => (hregular u hu).2.2.1) (fun u hu => (hregular u hu).2.2.2.2)
  have htE : t ∈ e.source := by rwa [hsrc]
  have hes : e s = 0 := by rw [heq s hsI]; exact sub_self _
  have het : e t = -Real.log (β t 2) := by
    rw [heq t htI]
    change Real.log (β s 2) - Real.log (β t 2) = _
    rw [hV, Real.log_one, zero_sub]
  have hEt : 0 ≤ e t := by simpa only [hes] using hmono.monotoneOn hsI htI hst
  have hEL : e t ≤ exitTailLength η α J := by
    have H := Real.log_le_log hh (hregion t htm).2.2.2.1.1
    rw [← exp_neg_exitTailLength hη.1 hα.1 J, Real.log_exp] at H
    rw [het]
    linarith only [H]
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
  let Y : ℝ → ExitTailState := fun z => toExitTailState (β (e.symm z))
  have hval (z : ℝ) (hz : z ∈ Icc 0 (e t)) : β (e.symm z) 2 = Real.exp (-z) := by
    have H := (hflow z (hzt z hz)).2.1
    change β (e.symm z) 2 = β s 2 * Real.exp (-z) at H
    simpa only [hV, one_mul] using H
  have hY (z : ℝ) (hz : z ∈ Icc 0 (e t)) : HasDerivAt Y (exitTailField (Real.exp (-z)) (Y z)) z := by
    have H := hasDerivAt_toExitTailState (hflow z (hzt z hz)).2.2
      (hv _ (hinv z hz)) (hm _ (hinv z hz))
    change HasDerivAt Y (exitTailField (β (e.symm z) 2) (Y z)) z at H
    rwa [hval z hz] at H
  have HY0 : Y 0 = toExitTailState (β s) := by dsimp only [Y]; rw [hinv0]
  have HYt : Y (e t) = toExitTailState (β t) := by dsimp only [Y]; rw [e.left_inv htE]
  have H := HP α b (e t) Y hα hb hsmall ⟨hEt, hEL⟩
    (by rw [HY0]; exact hR) (by rw [HY0]; exact hw) hY (e t) ⟨hEt, le_rfl⟩
  have Hvt : β t 2 = Real.exp (-(e t)) := by simpa only [e.left_inv htE] using hval (e t) ⟨hEt, le_rfl⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · have Hs := H.2.2.1
    rw [HYt] at Hs
    exact Hs
  · have Hr := H.2.2.2.1
    rw [HYt, HY0] at Hr
    exact Hr
  · have Hr := H.2.2.2.2.1
    rw [HYt] at Hr
    exact Hr
  · have Hu := H.2.2.2.2.2
    rw [HYt, ← Hvt] at Hu
    exact Hu

end BianchiIX
