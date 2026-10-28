import BianchiIX.Dynamics.ProjectiveFlowVariation
import BianchiIX.Dynamics.ReferenceEvents

noncomputable section

namespace BianchiIX

open Set

def referenceClock (k t : ℝ) : ℝ :=
  referenceClockPrimitive k t - referenceClockPrimitive k (-referenceHalfTime k)

theorem hasDerivAt_referenceClock (k t : ℝ) :
    HasDerivAt (referenceClock k) (projectiveStateDenom (referencePulse k t) / 6) t :=
  (hasDerivAt_referenceClockPrimitive k t).sub_const _

theorem referenceClock_entry (k : ℝ) : referenceClock k (-referenceHalfTime k) = 0 := sub_self _

theorem referenceClock_exit (k : ℝ) :
    referenceClock k (referenceHalfTime k) = referenceNormalizedTime k := by
  rw [referenceClock, ← referencePulse_clock_integral, referencePulse_crossing_time]

theorem referenceClock_normalized_orbit (k t : ℝ) :
    referenceClock k t ∈ normalizedMaxDomain (referenceEntryState k) 0 ∧
    normalizedMaxCurve (referenceEntryState k) 0 (referenceClock k t) =
      fromProjectiveState (referencePulse k t) := by
  obtain ⟨e, hsrc, he, _, _, _, _, _, hdom, hflow⟩ :=
    exists_projective_normalized_reparametrization (β := referencePulse k)
      (s := -referenceHalfTime k) convex_univ isOpen_univ (mem_univ _)
      (fun u _ => hasDerivAt_referencePulse k u) (fun u _ => referencePulse_denom_pos k u)
  have hmem : t ∈ e.source := by rw [hsrc]; trivial
  have ht : e t = referenceClock k t := by rw [he, referencePulse_clock_integral]; rfl
  have htarget : referenceClock k t ∈ e.target := ht ▸ e.map_source hmem
  have hinv : e.symm (referenceClock k t) = t := by rw [← ht, e.left_inv hmem]
  refine ⟨hdom htarget, ?_⟩
  have H := (hflow _ htarget).1
  rw [hinv] at H
  exact H.symm

theorem referenceClock_projective_orbit (k t : ℝ) :
    projectiveOriginalFlow (referencePulse k (-referenceHalfTime k)) 0 (referenceClock k t) =
      referencePulse k t := by
  change toProjectiveState (normalizedMaxCurve (referenceEntryState k) 0 (referenceClock k t)) = _
  rw [(referenceClock_normalized_orbit k t).2]
  exact toProjectiveState_fromProjectiveState (ne_of_gt (referencePulse_denom_pos k t))

theorem referenceClock_chart_pos (k t : ℝ) :
    0 < 1 + normalizedMaxCurve (referenceEntryState k) 0 (referenceClock k t) 0 := by
  rw [(referenceClock_normalized_orbit k t).2]
  exact fromProjectiveState_clock_pos (referencePulse_denom_pos k t)

def referenceActualVariation (k : ℝ) (w : ProjectiveState) (t : ℝ) : ProjectiveState :=
  projectiveFlowDifferential (referencePulse k (-referenceHalfTime k)) 0 (referenceClock k t) w

theorem referenceActualVariation_initial (k : ℝ) (w : ProjectiveState) :
    referenceActualVariation k w (-referenceHalfTime k) = w := by
  rw [referenceActualVariation, referenceClock_entry,
    projectiveFlowDifferential_initial (referencePulse_denom_pos k _)]
  rfl

theorem hasDerivAt_referenceActualVariation (k t : ℝ) (w : ProjectiveState) :
    HasDerivAt (referenceActualVariation k w)
      (referenceVariationVelocity k t (referenceActualVariation k w t)
        (-fderiv ℝ projectiveStateDenom (referencePulse k t) (referenceActualVariation k w t) /
          projectiveStateDenom (referencePulse k t))) t := by
  have H := hasDerivAt_projectiveFlowDifferential_apply (referencePulse_denom_pos k _)
    (referenceClock_normalized_orbit k t).1 (referenceClock_chart_pos k t) w
  rw [referenceClock_projective_orbit] at H
  exact hasDerivAt_referenceOriginalVariation
    (xi := fun s => projectiveFlowDifferential (referencePulse k (-referenceHalfTime k)) 0 s w)
    (clock := referenceClock k) H (hasDerivAt_referenceClock k t)

theorem referenceActualVariation_scattering {k : ℝ} (hk : 1 < k)
    {w : ProjectiveState} (hw : w 2 = 0) :
    referenceExitProjection k (referenceActualVariation k w (referenceHalfTime k)) =
      ![-w 0 + (2 / Real.sqrt (k ^ 2 - 1)) * (1 - Real.exp (-k * Real.arcosh k)) * w 1,
        Real.exp (-k * Real.arcosh k) * w 1, 0, Real.exp (-4 * Real.arcosh k / k) * w 3] := by
  have H := referenceVariation_scattering (I := univ) convex_univ hk
    (fun t _ => hasDerivAt_referenceActualVariation k t w) (mem_univ _) (mem_univ _)
    (by simpa only [referenceActualVariation_initial] using hw)
  simpa only [referenceActualVariation_initial] using H

/-- The matrix now acts on the actual exit-event derivative, with no variational premise. -/
theorem referenceCore_actual_derivative {k : ℝ} (hk : 1 < k)
    {w : ProjectiveState} (hw : w 2 = 0) :
    fderiv ℝ toProjectiveState (referenceExitState k)
      (normalizedEventDifferential projectiveActiveWall (referenceEntryState k) 0
        (referenceNormalizedTime k)
        (fderiv ℝ fromProjectiveState (referencePulse k (-referenceHalfTime k)) w)) =
      ![-w 0 + (2 / Real.sqrt (k ^ 2 - 1)) * (1 - Real.exp (-k * Real.arcosh k)) * w 1,
        Real.exp (-k * Real.arcosh k) * w 1, 0, Real.exp (-4 * Real.arcosh k / k) * w 3] := by
  rw [referenceCore_event_differential hk]
  have H := referenceActualVariation_scattering hk hw
  rw [referenceActualVariation, referenceClock_exit] at H
  unfold projectiveFlowDifferential at H
  change referenceExitProjection k
    (fderiv ℝ toProjectiveState
      (normalizedMaxCurve (referenceEntryState k) 0 (referenceNormalizedTime k))
      (normalizedFlowDifferential (referenceEntryState k) 0 (referenceNormalizedTime k)
        (fderiv ℝ fromProjectiveState (referencePulse k (-referenceHalfTime k)) w))) = _ at H
  rw [(referenceEntryState_crossing hk).2] at H
  exact H

end BianchiIX
