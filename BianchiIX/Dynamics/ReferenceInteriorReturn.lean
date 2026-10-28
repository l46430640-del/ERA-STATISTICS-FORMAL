import BianchiIX.Dynamics.ReferenceShiftedVariation
import BianchiIX.Dynamics.CoreAngleCharts
import BianchiIX.Dynamics.PartialCoreEntry

noncomputable section

namespace BianchiIX

open Set

theorem referencePulse_core_coordinates {k : ℝ} (hk : 0 < k) (s : ℝ) :
    toCoreAngleState (referencePulse k s) = ![k, 0, 0] ∧
      projectiveCoreAngle (referencePulse k s) = k * s := by
  have he : referencePulse k s = fromCoreAngleState (k * s) ![k, 0, 0] := by
    simp [referencePulse, fromCoreAngleState]
  rw [he]
  exact ⟨toCoreAngleState_fromCoreAngleState _ hk, projectiveCoreAngle_fromCoreAngleState _ hk.ne'⟩

theorem referencePulse_core_region {k s : ℝ} (hk : 6 ≤ k)
    (hs : s ∈ Ioo (-referenceHalfTime k) (referenceHalfTime k)) :
    coreRegion k (referencePulse k s) := by
  have hk0 : 0 < k := by linarith only [hk]
  have hR : coreRadius (referencePulse k s 0) (referencePulse k s 2) = k :=
    congrFun (referencePulse_core_coordinates hk0 s).1 0
  have H := partialCoreEntry_region (y := referencePulse k s) (ε := 1 / 10000)
    (by rw [hR]; exact hk) (referencePulse_above_section (by linarith only [hk]) hs).le
    (by simp [referencePulse]) (by simp [referencePulse]) le_rfl
    (by change 0 + _ * 0 ≤ _; rw [mul_zero, zero_add, hR]; positivity)
  rwa [hR] at H

/-- Every interior point of the boundary pulse reaches its first exit at the exact shifted clock. -/
theorem referencePulse_interior_firstReturn {k s : ℝ} (hk : 1 < k)
    (hs : s ∈ Ioo (-referenceHalfTime k) (referenceHalfTime k)) :
    let T := referenceShiftClock k s (referenceHalfTime k)
    0 < T ∧
      IsLeast {t | 0 < t ∧ t ∈ normalizedMaxDomain (fromProjectiveState (referencePulse k s)) 0 ∧
        projectiveOriginalFlow (referencePulse k s) 0 t 2 = 1} T ∧
      ∀ t ∈ Icc 0 T, t ∈ normalizedMaxDomain (fromProjectiveState (referencePulse k s)) 0 ∧
        0 < 1 + normalizedMaxCurve (fromProjectiveState (referencePulse k s)) 0 t 0 := by
  intro T
  have hmono := referenceShiftClock_strictMono k s
  have hpos : 0 < T := by
    simpa only [referenceShiftClock_initial] using hmono hs.2
  have hclock : Continuous (referenceShiftClock k s) :=
    continuous_iff_continuousAt.mpr fun r => (hasDerivAt_referenceShiftClock k s r).continuousAt
  have hparam (t : ℝ) (ht : t ∈ Icc 0 T) :
      ∃ r ∈ Icc s (referenceHalfTime k), referenceShiftClock k s r = t := by
    apply intermediate_value_Icc hs.2.le hclock.continuousOn
    simpa only [referenceShiftClock_initial] using ht
  refine ⟨hpos, ⟨⟨hpos, (referenceShiftClock_normalized_orbit k s _).1, ?_⟩, ?_⟩, ?_⟩
  · rw [referenceShiftClock_projective_orbit, referencePulse_exit hk]
    rfl
  · intro t ht
    by_contra! hlt
    obtain ⟨r, hr, he⟩ := hparam t ⟨ht.1.le, hlt.le⟩
    have hrlt : r < referenceHalfTime k := hmono.lt_iff_lt.mp (by rw [he]; exact hlt)
    have hv := referencePulse_above_section hk ⟨hs.1.trans_le hr.1, hrlt⟩
    have hh := ht.2.2
    rw [← he, referenceShiftClock_projective_orbit] at hh
    exact (ne_of_gt hv) hh
  · intro t ht
    obtain ⟨r, _, he⟩ := hparam t ht
    rw [← he]
    exact ⟨(referenceShiftClock_normalized_orbit k s r).1, referenceShiftClock_chart_pos k s r⟩

end BianchiIX
