import BianchiIX.Dynamics.CoreExistence
import BianchiIX.Dynamics.PartialCorePrefix

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

/-- Interior and incoming-boundary entries reach the outgoing section in the exact Einstein flow. -/
theorem exists_normalized_partialCore_return {x : NormalizedState} {t₀ s k : ℝ}
    (hc : stateConstraint x = 1) (hk : 6 ≤ k) (hs : t₀ ≤ s)
    (hA : 0 < 1 + normalizedMaxCurve x t₀ s 0) :
    let β := fun u => toProjectiveState (normalizedMaxCurve x t₀ u)
    coreRadius (β s 0) (β s 2) = k → (1 < β s 2 ∨ (β s 2 = 1 ∧ 1 ≤ β s 0)) →
    (0 ≤ β s 1 ∧ β s 1 ≤ (1 / 10000) / k) →
    (0 ≤ β s 2 * β s 3 ∧ β s 2 * β s 3 ≤ (1 / 10000) / k) →
    ∃ t > s, β t 2 = 1 ∧ ∀ u ∈ Icc s t,
      3 / (2 * k ^ 2) ≤ 1 + normalizedMaxCurve x t₀ u 0 ∧ coreRegion k (β u) := by
  intro β hR hVcase hU hP
  have hk0 : 0 < k := by linarith
  let c := 3 / (2 * k ^ 2)
  have hc0 : 0 < c := by dsimp [c]; positivity
  let S : Set ℝ := {u | c ≤ 1 + normalizedMaxCurve x t₀ u 0 ∧ coreRegion k (β u)}
  let T := s + 2 * k * Real.log (4 * k) + 1
  have hlog : 0 < Real.log (4 * k) := Real.log_pos (by linarith)
  have hsT : s ≤ T := by
    dsimp [T]
    have H : 0 < 2 * k * Real.log (4 * k) := by positivity
    linarith
  have hE : |coreEnergy (β s 0) (β s 2) - k ^ 2| < 1 / 8 := by
    rw [← coreRadius_sq, hR, sub_self, abs_zero]
    norm_num
  obtain ⟨r₀, hr₀, hprefix⟩ := normalized_core_local_prefix hc hk hs hA hE hVcase hU hP
  have hsS : s ∈ S := ⟨(hprefix s ⟨le_rfl, hr₀.le⟩).1.le, (hprefix s ⟨le_rfl, hr₀.le⟩).2⟩
  by_contra hnone
  have hwhole : Icc s T ⊆ S := by
    apply (isClosed_normalized_core_times hc hk hs).Icc_subset_of_forall_mem_nhdsGT_of_Icc_subset hsS
    intro t ht hbefore
    have htS := hbefore ⟨ht.1, le_rfl⟩
    have hAt : 0 < 1 + normalizedMaxCurve x t₀ t 0 := hc0.trans_le htS.1
    have hAbefore (u : ℝ) (hu : u ∈ Icc s t) : 0 < 1 + normalizedMaxCurve x t₀ u 0 :=
      hc0.trans_le (hbefore hu).1
    have henergy := (normalized_partialCore_energy_band_improves hc hk hs ht.1 hAbefore hR
      (fun u hu => by rw [coreRadius_sq]; exact (hbefore hu).2.1)
      (fun u hu => (hbefore hu).2.2.1) (fun u hu => (hbefore hu).2.2.2.1)
      (fun u hu => (hbefore hu).2.2.2.2)).2
    have hstrict : |coreEnergy (β t 0) (β t 2) - k ^ 2| < 1 / 8 := by
      rw [coreRadius_sq] at henergy
      linarith
    have hvcase : 1 < β t 2 ∨ (β t 2 = 1 ∧ 1 ≤ β t 0) := by
      rcases eq_or_lt_of_le ht.1 with heq | hst
      · subst t
        exact hVcase
      · left
        apply lt_of_le_of_ne htS.2.2.1
        intro heq
        exact hnone ⟨t, hst, heq.symm, fun u hu => hbefore hu⟩
    obtain ⟨r, htr, hafter⟩ := normalized_core_local_prefix hc hk (hs.trans ht.1) hAt hstrict hvcase
      htS.2.2.2.1 htS.2.2.2.2
    apply mem_nhdsGT_iff_exists_Ioc_subset.mpr
    exact ⟨r, htr, fun u hu => ⟨(hafter u ⟨hu.1.le, hu.2⟩).1.le, (hafter u ⟨hu.1.le, hu.2⟩).2⟩⟩
  have H := (normalized_core_residence hc hk hs hsT (fun u hu => hc0.trans_le (hwhole hu).1)
    (fun u hu => coreRegion_radius_bounds hk (hwhole hu).2)
    (fun u hu => (hwhole hu).2.2.1)
    (fun u hu => (coreRegion_wall_bounds (hwhole hu).2).1)
    (fun u hu => (coreRegion_wall_bounds (hwhole hu).2).2)).2
  dsimp [T] at H
  linarith

end BianchiIX
