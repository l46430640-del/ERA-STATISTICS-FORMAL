import BianchiIX.Dynamics.ExitActualPrefix
import BianchiIX.Dynamics.ExitLocalPrefix
import BianchiIX.Dynamics.ExitResidence
import Mathlib.Topology.Order.IntermediateValue

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

theorem isClosed_normalized_exit_times {x : NormalizedState} {t₀ s T h : ℝ}
    (hc : stateConstraint x = 1) (hs : t₀ ≤ s) :
    IsClosed ({u | 1 / 16 ≤ 1 + normalizedMaxCurve x t₀ u 0 ∧
      exitPhysicalRegion h (toProjectiveState (normalizedMaxCurve x t₀ u))} ∩ Icc s T) := by
  let a := fun u => 1 + normalizedMaxCurve x t₀ u 0
  let β := fun u => toProjectiveState (normalizedMaxCurve x t₀ u)
  have hα (u : ℝ) (hu : u ∈ Icc s T) :=
    (normalizedMaxCurve_forward_of_constraint hc (hs.trans hu.1)).1.continuousAt
  have ha : ContinuousOn a (Icc s T) := fun u hu =>
    (continuousAt_const.add ((continuous_apply 0).continuousAt.comp (hα u hu))).continuousWithinAt
  have hD : IsClosed (Icc s T ∩ {u | (1 : ℝ) / 16 ≤ a u}) :=
    ha.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have hβ : ContinuousOn β (Icc s T ∩ {u | (1 : ℝ) / 16 ≤ a u}) := by
    intro u hu
    have hAu : 0 < 1 + normalizedMaxCurve x t₀ u 0 := lt_of_lt_of_le (by norm_num) hu.2
    exact ((contDiffAt_toProjectiveState 1 (ne_of_gt hAu)).continuousAt.comp (hα u hu.1)).continuousWithinAt
  have H := hβ.preimage_isClosed_of_isClosed hD (isClosed_exitPhysicalRegion h)
  convert! H using 1
  ext u
  change (1 / 16 ≤ a u ∧ exitPhysicalRegion h (β u)) ∧ u ∈ Icc s T ↔
    (u ∈ Icc s T ∧ 1 / 16 ≤ a u) ∧ exitPhysicalRegion h (β u)
  tauto

/-- The exact signed Einstein flow reaches the parameter-dependent exit height. -/
theorem exists_normalized_exit_arrival {η : ℝ} (hη : 0 < η ∧ η < 1) {J : ℕ} (hJ : 1 ≤ J) :
    ∃ A ≥ (2 : ℝ), ∃ ε > (0 : ℝ), ∀ (x : NormalizedState) (t₀ s α b : ℝ),
      stateConstraint x = 1 → t₀ ≤ s → (0 < α ∧ α ≤ 1) → 0 < b → b ≤ ε * α ^ J →
      0 < 1 + normalizedMaxCurve x t₀ s 0 →
      let β := fun u => toProjectiveState (normalizedMaxCurve x t₀ u)
      β s 0 < 0 → β s 2 = 1 → coreRadius (β s 0) (β s 2) = 2 + 2 * α →
      |β s 1| + |β s 3| ≤ b →
      ∃ t > s, β t 2 = η * α ^ J ∧
        (∀ u ∈ Icc s t, 1 / 16 ≤ 1 + normalizedMaxCurve x t₀ u 0 ∧
          exitPhysicalRegion (η * α ^ J) (β u)) ∧
        t - s ≤ 16 * exitTailLength η α J ∧
        (∀ u ∈ Icc s t, |β u 1| + |β u 3| ≤ A * b / 2 ∧
          |coreRadius (β u 0) (β u 2) - coreRadius (β s 0) (β s 2)| ≤ 40 * A * b ∧
          2 + α < coreRadius (β u 0) (β u 2) ∧ |β u 1| ≤ β u 2 / 2) := by
  obtain ⟨A, hA, ε₀, hε₀, HP⟩ := exists_normalized_exit_prefix_bounds ⟨hη.1, hη.2.le⟩ hJ
  have hA0 : 0 < A := by linarith only [hA]
  let ε := min ε₀ (1 / (1000 * A))
  have hε : 0 < ε := lt_min hε₀ (by positivity)
  refine ⟨A, hA, ε, hε, ?_⟩
  intro x t₀ s α b hc hs hα hb hsmall hAinit β hM hV hR hw
  let h := η * α ^ J
  have hh : 0 < h := mul_pos hη.1 (pow_pos hα.1 J)
  have hh1 : h < 1 := by
    have H := mul_le_mul_of_nonneg_left (pow_le_one₀ hα.1.le hα.2 (n := J)) hη.1.le
    dsimp only [h]
    nlinarith only [H, hη.2]
  have hbε : b ≤ ε := hsmall.trans (by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (pow_le_one₀ hα.1.le hα.2 (n := J)) hε.le)
  have hAb : A * b ≤ 1 / 1000 := by
    have H := (le_div_iff₀ (by positivity : 0 < 1000 * A)).mp (hbε.trans (min_le_right _ _))
    nlinarith only [H]
  have hbsmall : b ≤ ε₀ * α ^ J :=
    hsmall.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (pow_nonneg hα.1.le J))
  have hprefix (t : ℝ) (hst : s ≤ t)
      (hAf : ∀ u ∈ Icc s t, 0 < 1 + normalizedMaxCurve x t₀ u 0)
      (hreg : ∀ u ∈ Icc s t, exitPhysicalRegion h (β u)) :=
    HP x t₀ s t α b hc hs hst hα hb hbsmall hAf hreg hV hR hw
  have hRstrict : 7 / 4 < coreRadius (β s 0) (β s 2) ∧ coreRadius (β s 0) (β s 2) < 17 / 4 := by
    rw [hR]
    constructor <;> linarith only [hα.1, hα.2]
  have hbs : b ≤ 1 / 1000 := by nlinarith only [hA, hb, hAb]
  have hus : |β s 1| < 1 / 100 := by linarith only [hw, hbs, abs_nonneg (β s 3)]
  have hws : |β s 3| < 1 / 100 := by linarith only [hw, hbs, abs_nonneg (β s 1)]
  have hvs : h < β s 2 ∧ β s 2 ≤ 1 := by rw [hV]; exact ⟨hh1, le_rfl⟩
  obtain ⟨r₀, hr₀, hlocal⟩ := normalized_exit_local_prefix hc hh hs hAinit hM hRstrict hus hvs hws
  let S : Set ℝ := {u | 1 / 16 ≤ 1 + normalizedMaxCurve x t₀ u 0 ∧ exitPhysicalRegion h (β u)}
  have hsS : s ∈ S := ⟨(hlocal s ⟨le_rfl, hr₀.le⟩).1.le, (hlocal s ⟨le_rfl, hr₀.le⟩).2⟩
  have hex : ∃ t > s, β t 2 = h ∧ ∀ u ∈ Icc s t, u ∈ S := by
    by_contra hnone
    let T := s + 16 * exitTailLength η α J + 1
    have hL := exitTailLength_nonneg ⟨hη.1, hη.2.le⟩ hα J
    have hsT : s ≤ T := by dsimp only [T]; linarith only [hL]
    have hwhole : Icc s T ⊆ S := by
      apply (isClosed_normalized_exit_times hc hs).Icc_subset_of_forall_mem_nhdsGT_of_Icc_subset hsS
      intro t ht hbefore
      have htS := hbefore ⟨ht.1, le_rfl⟩
      have hAf (u : ℝ) (hu : u ∈ Icc s t) : 0 < 1 + normalizedMaxCurve x t₀ u 0 :=
        lt_of_lt_of_le (by norm_num) (hbefore hu).1
      have H := hprefix t ht.1 hAf (fun u hu => (hbefore hu).2)
      have hu : |β t 1| < 1 / 100 := by linarith only [H.1, hAb, abs_nonneg (β t 3)]
      have hw' : |β t 3| < 1 / 100 := by linarith only [H.1, hAb, abs_nonneg (β t 1)]
      have hRt : 7 / 4 < coreRadius (β t 0) (β t 2) ∧ coreRadius (β t 0) (β t 2) < 17 / 4 := by
        have Hr := H.2.1
        rw [hR] at Hr
        constructor
        · linarith only [H.2.2.1, hα.1]
        · linarith only [(abs_le.mp Hr).2, hα.2, hAb]
      have hvlt : h < β t 2 := by
        rcases eq_or_lt_of_le ht.1 with heq | hst
        · subst t
          exact hvs.1
        · apply lt_of_le_of_ne htS.2.2.2.2.1.1
          intro heq
          exact hnone ⟨t, hst, heq.symm, fun u hu => hbefore hu⟩
      obtain ⟨r, htr, hafter⟩ := normalized_exit_local_prefix hc hh (hs.trans ht.1) (hAf t ⟨ht.1, le_rfl⟩)
        (exitPhysicalRegion_phase_bounds hh htS.2).2 hRt hu ⟨hvlt, htS.2.2.2.2.1.2⟩ hw'
      apply mem_nhdsGT_iff_exists_Ioc_subset.mpr
      exact ⟨r, htr, fun u hu => ⟨(hafter u ⟨hu.1.le, hu.2⟩).1.le, (hafter u ⟨hu.1.le, hu.2⟩).2⟩⟩
    have H := (normalized_exit_residence hc hh hs hsT
      (fun u hu => lt_of_lt_of_le (by norm_num) (hwhole hu).1) (fun u hu => (hwhole hu).2) hV).2
    have hlog : Real.log (1 / h) = exitTailLength η α J := by
      rw [one_div, Real.log_inv]
      change -Real.log (η * α ^ J) = _
      rw [← exp_neg_exitTailLength hη.1 hα.1 J, Real.log_exp, neg_neg]
    rw [hlog] at H
    dsimp only [T] at H
    linarith only [H]
  obtain ⟨t, hst, hhit, hwhole⟩ := hex
  have hAf (u : ℝ) (hu : u ∈ Icc s t) : 0 < 1 + normalizedMaxCurve x t₀ u 0 :=
    lt_of_lt_of_le (by norm_num) (hwhole u hu).1
  refine ⟨t, hst, hhit, hwhole, ?_, ?_⟩
  · have H := (normalized_exit_residence hc hh hs hst.le hAf (fun u hu => (hwhole u hu).2) hV).2
    have he : Real.log (1 / h) = exitTailLength η α J := by
      rw [one_div, Real.log_inv]
      change -Real.log (η * α ^ J) = _
      rw [← exp_neg_exitTailLength hη.1 hα.1 J, Real.log_exp, neg_neg]
    rwa [he] at H
  · intro u hu
    exact hprefix u hu.1 (fun q hq => hAf q ⟨hq.1, hq.2.trans hu.2⟩)
      (fun q hq => (hwhole q ⟨hq.1, hq.2.trans hu.2⟩).2)

end BianchiIX
