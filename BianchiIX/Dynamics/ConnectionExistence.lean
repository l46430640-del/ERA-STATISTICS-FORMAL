import BianchiIX.Dynamics.ConnectionEntry
import BianchiIX.Dynamics.ConnectionResidence
import Mathlib.Topology.Order.IntermediateValue

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

theorem isClosed_normalized_connection_times {x : NormalizedState} {t₀ s T μ : ℝ}
    (hc : stateConstraint x = 1) (hμ : 4 ≤ μ) (hs : t₀ ≤ s) :
    IsClosed ({u | 3 / (2 * μ ^ 2) ≤ 1 + normalizedMaxCurve x t₀ u 0 ∧
      connectionRegion μ (toProjectiveState (normalizedMaxCurve x t₀ u))} ∩ Icc s T) := by
  let a := fun u => 1 + normalizedMaxCurve x t₀ u 0
  let β := fun u => toProjectiveState (normalizedMaxCurve x t₀ u)
  let c := 3 / (2 * μ ^ 2)
  have hc0 : 0 < c := by
    dsimp [c]
    have hμ0 : 0 < μ := by linarith only [hμ]
    positivity
  have hα (u : ℝ) (hu : u ∈ Icc s T) : ContinuousAt (normalizedMaxCurve x t₀) u :=
    (normalizedMaxCurve_forward_of_constraint hc (hs.trans hu.1)).1.continuousAt
  have ha : ContinuousOn a (Icc s T) := fun u hu =>
    (continuousAt_const.add ((continuous_apply 0).continuousAt.comp (hα u hu))).continuousWithinAt
  have hD : IsClosed (Icc s T ∩ {u | c ≤ a u}) :=
    ha.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have hβ : ContinuousOn β (Icc s T ∩ {u | c ≤ a u}) := by
    intro u hu
    have hAu : 0 < 1 + normalizedMaxCurve x t₀ u 0 := hc0.trans_le hu.2
    exact ((contDiffAt_toProjectiveState 1 (ne_of_gt hAu)).continuousAt.comp (hα u hu.1)).continuousWithinAt
  have H := hβ.preimage_isClosed_of_isClosed hD (isClosed_connectionRegion μ)
  convert! H using 1
  ext u
  change (c ≤ a u ∧ connectionRegion μ (β u)) ∧ u ∈ Icc s T ↔
    (u ∈ Icc s T ∧ c ≤ a u) ∧ connectionRegion μ (β u)
  tauto

/-- The actual flow reaches the next wall while remaining in the closed connection region. -/
theorem exists_normalized_connection_return {x : NormalizedState} {t₀ s μ : ℝ}
    (hc : stateConstraint x = 1) (hμ : 4 ≤ μ) (hs : t₀ ≤ s)
    (hA : 0 < 1 + normalizedMaxCurve x t₀ s 0) :
    let β := fun u => toProjectiveState (normalizedMaxCurve x t₀ u);
    -β s 0 = μ → β s 2 = 1 →
    (0 ≤ β s 1 ∧ β s 1 ≤ 1 / 10000) → (0 < β s 3 ∧ β s 3 < 1) →
    ∃ t > s, β t 3 = 1 ∧ ∀ u ∈ Icc s t,
      3 / (2 * μ ^ 2) ≤ 1 + normalizedMaxCurve x t₀ u 0 ∧ connectionRegion μ (β u) := by
  intro β hM hV hU hW
  have hμ0 : 0 < μ := by linarith only [hμ]
  let c := 3 / (2 * μ ^ 2)
  have hc0 : 0 < c := by dsimp [c]; positivity
  let S : Set ℝ := {u | c ≤ 1 + normalizedMaxCurve x t₀ u 0 ∧ connectionRegion μ (β u)}
  let T := s + μ * Real.log (1 / β s 3) + 1
  have hlog : 0 ≤ Real.log (1 / β s 3) := by
    rw [one_div, Real.log_inv]
    exact neg_nonneg.mpr (Real.log_nonpos hW.1.le hW.2.le)
  have hsT : s ≤ T := by
    dsimp [T]
    nlinarith only [mul_nonneg hμ0.le hlog]
  have hm : |-β s 0 - μ| < 1 / 2 := by rw [hM, sub_self, abs_zero]; norm_num
  have hv : 0 < β s 2 ∧ β s 2 ≤ 1 := by rw [hV]; norm_num
  have hentry : β s 1 ≤ β s 2 := by rw [hV]; linarith only [hU.2]
  obtain ⟨r₀, hr₀, hprefix⟩ := normalized_connection_local_prefix hc hμ hs hA hm hU hv hW
  have hsS : s ∈ S := ⟨(hprefix s ⟨le_rfl, hr₀.le⟩).1.le, (hprefix s ⟨le_rfl, hr₀.le⟩).2⟩
  have hdom (u : ℝ) (hu : s ≤ u) : u ∈ normalizedMaxDomain x t₀ :=
    normalizedMaxDomain_contains_Ici_of_constraint hc t₀ (hs.trans hu)
  have hpositive (u : ℝ) (hu : s ≤ u) (hAu : 0 < 1 + normalizedMaxCurve x t₀ u 0) :
      0 < β u 2 ∧ 0 < β u 3 :=
    ⟨normalized_projective_wall_pos (hdom s le_rfl) (hdom u hu) hA hAu 1 hv.1,
      normalized_projective_wall_pos (hdom s le_rfl) (hdom u hu) hA hAu 2 hW.1⟩
  by_contra hnone
  have hwhole : Icc s T ⊆ S := by
    apply (isClosed_normalized_connection_times hc hμ hs).Icc_subset_of_forall_mem_nhdsGT_of_Icc_subset hsS
    intro t ht hbefore
    have htS := hbefore ⟨ht.1, le_rfl⟩
    have hAt : 0 < 1 + normalizedMaxCurve x t₀ t 0 := hc0.trans_le htS.1
    have hAbefore (u : ℝ) (hu : u ∈ Icc s t) : 0 < 1 + normalizedMaxCurve x t₀ u 0 :=
      hc0.trans_le (hbefore hu).1
    have hpos (u : ℝ) (hu : u ∈ Icc s t) := hpositive u hu.1 (hAbefore u hu)
    have hstrict := (normalized_connection_phase_band_improves hc hμ hs ht.1 hAbefore hM
      (fun u hu => (hbefore hu).2.1) (fun u hu => (hbefore hu).2.2.1)
      (fun u hu => ⟨(hpos u hu).1, (hbefore hu).2.2.2.1.2⟩)
      (fun u hu => ⟨(hpos u hu).2, (hbefore hu).2.2.2.2.2⟩) hentry).2
    have hwlt : β t 3 < 1 := by
      rcases eq_or_lt_of_le ht.1 with heq | hst
      · subst t
        exact hW.2
      · apply lt_of_le_of_ne htS.2.2.2.2.2
        intro heq
        exact hnone ⟨t, hst, heq, fun u hu => hbefore hu⟩
    obtain ⟨r, htr, hafter⟩ := normalized_connection_local_prefix hc hμ (hs.trans ht.1) hAt
      hstrict htS.2.2.1 ⟨(hpositive t ht.1 hAt).1, htS.2.2.2.1.2⟩
      ⟨(hpositive t ht.1 hAt).2, hwlt⟩
    apply mem_nhdsGT_iff_exists_Ioc_subset.mpr
    exact ⟨r, htr, fun u hu => ⟨(hafter u ⟨hu.1.le, hu.2⟩).1.le, (hafter u ⟨hu.1.le, hu.2⟩).2⟩⟩
  have H := (normalized_connection_residence hc hμ hs hsT
    (fun u hu => hc0.trans_le (hwhole hu).1) (fun u hu => (hwhole hu).2)
    (fun u hu => (hpositive u hu.1 (hc0.trans_le (hwhole hu).1)).2)).2
  dsimp [T] at H
  linarith only [H]

def connectionEntry (μ u w : ℝ) : ProjectiveState := ![-μ, u, 1, w]

/-- The stated entry range has an actual next-wall hit; zero strong wall is included. -/
theorem exists_connection_return {μ u w : ℝ} (hμ : 4 ≤ μ)
    (hu : 0 ≤ u ∧ u ≤ (1 / 10000) / μ) (hw : 0 < w ∧ w ≤ 1 / 10000) :
    let x := fromProjectiveState (connectionEntry μ u w)
    let β := fun t => toProjectiveState (normalizedMaxCurve x 0 t)
    ∃ T > (0 : ℝ), β T 3 = 1 ∧ ∀ t ∈ Icc 0 T,
      3 / (2 * μ ^ 2) ≤ 1 + normalizedMaxCurve x 0 t 0 ∧ connectionRegion μ (β t) := by
  intro x β
  have hμ1 : 1 ≤ μ := by linarith only [hμ]
  have hu' : 0 ≤ u ∧ u ≤ 1 / 10000 :=
    ⟨hu.1, hu.2.trans (div_le_self (by norm_num) hμ1)⟩
  have hw' : 0 < w ∧ w < 1 := ⟨hw.1, lt_of_le_of_lt hw.2 (by norm_num)⟩
  have hD : 0 < projectiveStateDenom (connectionEntry μ u w) :=
    (connection_denom_bound (m := μ) (v := 1) hu' (by norm_num) ⟨hw.1.le, hw'.2.le⟩).2
  have hc : stateConstraint x = 1 := fromProjectiveState_constraint (ne_of_gt hD)
  have hβ0 : β 0 = connectionEntry μ u w := by
    dsimp [β]
    rw [normalizedMaxCurve_initial]
    exact toProjectiveState_fromProjectiveState (ne_of_gt hD)
  have hA : 0 < 1 + normalizedMaxCurve x 0 0 0 := by
    rw [normalizedMaxCurve_initial]
    exact fromProjectiveState_clock_pos hD
  apply exists_normalized_connection_return hc hμ (le_refl 0) hA
  · change -β 0 0 = μ
    rw [hβ0]
    simp [connectionEntry]
  · change β 0 2 = 1
    rw [hβ0]
    rfl
  · change 0 ≤ β 0 1 ∧ β 0 1 ≤ 1 / 10000
    simpa only [hβ0, connectionEntry, Matrix.cons_val_one, Matrix.cons_val_zero] using hu'
  · change 0 < β 0 3 ∧ β 0 3 < 1
    simpa [hβ0, connectionEntry] using hw'

end BianchiIX
