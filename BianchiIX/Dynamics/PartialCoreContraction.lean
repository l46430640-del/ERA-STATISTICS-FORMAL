import BianchiIX.Analysis.PartialCoreAngleGap
import BianchiIX.Dynamics.PartialCoreFirstReturn

noncomputable section

namespace BianchiIX

open Set

theorem normalized_partialCore_exit_contraction {x : NormalizedState} {t₀ s t k Z : ℝ}
    (hc : stateConstraint x = 1) (hk : 6 ≤ k) (hs : t₀ ≤ s) (hst : s < t)
    (hZ : 0 ≤ Z) (hkZ : 2 * Real.cosh Z ≤ k)
    (hA : ∀ u ∈ Icc s t, 0 < 1 + normalizedMaxCurve x t₀ u 0) :
    let β := fun u => toProjectiveState (normalizedMaxCurve x t₀ u)
    (∀ u ∈ Icc s t, coreRegion k (β u)) →
    coreAngle (β s 0) (β s 2) ≤ Z → β t 2 = 1 →
    Real.log (99 / 50 : ℝ) ≤ coreAngle (β t 0) (β t 2) - coreAngle (β s 0) (β s 2) ∧
      49 / 99 ≤ coreAngle (β t 0) (β t 2) - coreAngle (β s 0) (β s 2) ∧
      β t 1 ≤ β s 1 * Real.exp (-k / 12) ∧ β t 3 ≤ β s 2 * β s 3 := by
  intro β hregion hz₀ hvt
  have hsm : s ∈ Icc s t := ⟨le_rfl, hst.le⟩
  have htm : t ∈ Icc s t := ⟨hst.le, le_rfl⟩
  have hk0 : 0 < k := by linarith only [hk]
  have hr (u : ℝ) (hu : u ∈ Icc s t) := coreRegion_radius_bounds hk (hregion u hu)
  have hw (u : ℝ) (hu : u ∈ Icc s t) := coreRegion_wall_bounds (hregion u hu)
  have hv (u : ℝ) (hu : u ∈ Icc s t) : 1 ≤ β u 2 := (hregion u hu).2.1
  have hout := normalized_core_return_downward hc hk hs hst (hA t htm) hvt
    (fun u hu => hv u ⟨hu.1.le, hu.2.le⟩) (hr t htm).1 (hw t htm).1 (hw t htm).2
  have hcosh : 99 / 100 * k ≤ Real.cosh (coreAngle (β t 0) (β t 2)) := by
    rw [cosh_coreAngle (zero_lt_one.trans_le (hv t htm)), hvt, div_one]
    simpa only [hvt] using (hr t htm).1
  obtain ⟨hgap, hgap', hgap3⟩ := partial_core_angle_gap hk0 hZ hz₀ hout.2.1.le
    (by linarith only [hkZ]) hcosh
  have hdom : Icc s t ⊆ normalizedMaxDomain x t₀ := fun _ hu =>
    normalizedMaxDomain_contains_Ici_of_constraint hc t₀ (hs.trans hu.1)
  obtain ⟨hU, hP⟩ := normalized_core_prefix_contraction hk (convex_Icc s t) hdom hc hA
    hsm htm hst.le (fun u hu => (hr u hu).1) hv
    (fun u hu => (hw u hu).1) (fun u hu => (hw u hu).2)
  have hexp : -k * (coreAngle (β t 0) (β t 2) - coreAngle (β s 0) (β s 2)) / 4 ≤ -k / 12 := by
    have H := mul_le_mul_of_nonneg_left hgap3.le hk0.le
    linarith only [H]
  change β t 2 * β t 3 ≤ β s 2 * β s 3 at hP
  rw [hvt, one_mul] at hP
  exact ⟨hgap, hgap', hU.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (hw s hsm).1.1), hP⟩

end BianchiIX
