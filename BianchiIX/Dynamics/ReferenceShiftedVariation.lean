import BianchiIX.Dynamics.ReferenceActualVariation

noncomputable section

namespace BianchiIX

open Set

def referenceShiftClock (k s t : ℝ) : ℝ :=
  referenceClockPrimitive k t - referenceClockPrimitive k s

theorem hasDerivAt_referenceShiftClock (k s t : ℝ) :
    HasDerivAt (referenceShiftClock k s) (projectiveStateDenom (referencePulse k t) / 6) t :=
  (hasDerivAt_referenceClockPrimitive k t).sub_const _

theorem referenceShiftClock_initial (k s : ℝ) : referenceShiftClock k s s = 0 := sub_self _

theorem referenceShiftClock_strictMono (k s : ℝ) : StrictMono (referenceShiftClock k s) := by
  apply strictMono_of_deriv_pos
  intro t
  rw [(hasDerivAt_referenceShiftClock k s t).deriv]
  exact div_pos (referencePulse_denom_pos k t) (by norm_num)

theorem referenceShiftClock_normalized_orbit (k s t : ℝ) :
    referenceShiftClock k s t ∈ normalizedMaxDomain (fromProjectiveState (referencePulse k s)) 0 ∧
      normalizedMaxCurve (fromProjectiveState (referencePulse k s)) 0 (referenceShiftClock k s t) =
        fromProjectiveState (referencePulse k t) := by
  obtain ⟨e, hsrc, he, _, _, _, _, _, hdom, hflow⟩ :=
    exists_projective_normalized_reparametrization (β := referencePulse k)
      (s := s) convex_univ isOpen_univ (mem_univ _)
      (fun u _ => hasDerivAt_referencePulse k u) (fun u _ => referencePulse_denom_pos k u)
  have hmem : t ∈ e.source := by rw [hsrc]; trivial
  have ht : e t = referenceShiftClock k s t := by rw [he, referencePulse_clock_integral]; rfl
  have htarget : referenceShiftClock k s t ∈ e.target := ht ▸ e.map_source hmem
  have hinv : e.symm (referenceShiftClock k s t) = t := by rw [← ht, e.left_inv hmem]
  refine ⟨hdom htarget, ?_⟩
  have H := (hflow _ htarget).1
  rw [hinv] at H
  exact H.symm

theorem referenceShiftClock_projective_orbit (k s t : ℝ) :
    projectiveOriginalFlow (referencePulse k s) 0 (referenceShiftClock k s t) = referencePulse k t := by
  unfold projectiveOriginalFlow
  rw [(referenceShiftClock_normalized_orbit k s t).2]
  exact toProjectiveState_fromProjectiveState (referencePulse_denom_pos k t).ne'

theorem referenceShiftClock_chart_pos (k s t : ℝ) :
    0 < 1 + normalizedMaxCurve (fromProjectiveState (referencePulse k s)) 0
      (referenceShiftClock k s t) 0 := by
  rw [(referenceShiftClock_normalized_orbit k s t).2]
  exact fromProjectiveState_clock_pos (referencePulse_denom_pos k t)

def referenceShiftedVariation (k s : ℝ) (w : ProjectiveState) (t : ℝ) : ProjectiveState :=
  projectiveFlowDifferential (referencePulse k s) 0 (referenceShiftClock k s t) w

theorem referenceShiftedVariation_initial (k s : ℝ) (w : ProjectiveState) :
    referenceShiftedVariation k s w s = w := by
  rw [referenceShiftedVariation, referenceShiftClock_initial,
    projectiveFlowDifferential_initial (referencePulse_denom_pos k s)]
  rfl

theorem hasDerivAt_referenceShiftedVariation (k s t : ℝ) (w : ProjectiveState) :
    HasDerivAt (referenceShiftedVariation k s w)
      (referenceVariationVelocity k t (referenceShiftedVariation k s w t)
        (-fderiv ℝ projectiveStateDenom (referencePulse k t) (referenceShiftedVariation k s w t) /
          projectiveStateDenom (referencePulse k t))) t := by
  have H := hasDerivAt_projectiveFlowDifferential_apply (referencePulse_denom_pos k s)
    (referenceShiftClock_normalized_orbit k s t).1 (referenceShiftClock_chart_pos k s t) w
  rw [referenceShiftClock_projective_orbit] at H
  exact hasDerivAt_referenceOriginalVariation
    (xi := fun r => projectiveFlowDifferential (referencePulse k s) 0 r w)
    (clock := referenceShiftClock k s) H (hasDerivAt_referenceShiftClock k s t)

end BianchiIX
