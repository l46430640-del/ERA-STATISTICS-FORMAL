import BianchiIX.Dynamics.Events
import BianchiIX.Dynamics.ProjectiveRegularity
import BianchiIX.Dynamics.ReferenceScattering

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

def referenceEntryState (k : ℝ) : NormalizedState :=
  fromProjectiveState (referencePulse k (-referenceHalfTime k))

def referenceExitState (k : ℝ) : NormalizedState :=
  fromProjectiveState (referencePulse k (referenceHalfTime k))

theorem referenceExitState_clock_pos (k : ℝ) : 0 < 1 + referenceExitState k 0 :=
  fromProjectiveState_clock_pos (referencePulse_denom_pos k _)

theorem referenceExitState_constraint (k : ℝ) : stateConstraint (referenceExitState k) = 1 :=
  fromProjectiveState_constraint (ne_of_gt (referencePulse_denom_pos k _))

theorem referenceExitState_projective (k : ℝ) :
    toProjectiveState (referenceExitState k) = referencePulse k (referenceHalfTime k) :=
  toProjectiveState_fromProjectiveState (ne_of_gt (referencePulse_denom_pos k _))

theorem referenceEntryState_crossing {k : ℝ} (hk : 1 < k) :
    referenceNormalizedTime k ∈ normalizedMaxDomain (referenceEntryState k) 0 ∧
    normalizedMaxCurve (referenceEntryState k) 0 (referenceNormalizedTime k) = referenceExitState k := by
  have H := referencePulse_normalized_crossing hk
  refine ⟨?_, ?_⟩
  · simpa only [referenceEntryState, referencePulse_entry hk] using
      H.1 ⟨(referenceNormalizedTime_pos hk).le, le_rfl⟩
  · simpa only [referenceEntryState, referenceExitState, referencePulse_entry hk,
      referencePulse_exit hk] using H.2.1

theorem referenceExitState_rate_neg {k : ℝ} (hk : 1 < k) :
    fderiv ℝ projectiveActiveWall (referenceExitState k) (normalizedField (referenceExitState k)) < 0 := by
  rw [projectiveActiveWall_fderiv_field (ne_of_gt (referenceExitState_clock_pos k))
    (referenceExitState_constraint k), referenceExitState_projective, referencePulse_exit_field hk]
  exact mul_neg_of_pos_of_neg (referenceExitState_clock_pos k) (neg_neg_of_pos (referenceCoreGap_pos hk))

/-- This event is built from the actual original flow and has its genuine initial-state derivative. -/
theorem exists_referenceCore_event {k : ℝ} (hk : 1 < k) :
    ∃ tau : NormalizedState → ℝ,
      tau (referenceEntryState k) = referenceNormalizedTime k ∧
      ContDiffAt ℝ 1 tau (referenceEntryState k) ∧
      HasFDerivAt tau
        (normalizedEventTimeDifferential projectiveActiveWall (referenceEntryState k) 0
          (referenceNormalizedTime k)) (referenceEntryState k) ∧
      (∀ᶠ y in 𝓝 (referenceEntryState k), tau y ∈ normalizedMaxDomain y 0 ∧
        projectiveActiveWall (normalizedMaxCurve y 0 (tau y)) = 1) ∧
      (∀ᶠ z : NormalizedState × ℝ in 𝓝 (referenceEntryState k, referenceNormalizedTime k),
        z.2 ∈ normalizedMaxDomain z.1 0 ∧
        (projectiveActiveWall (normalizedMaxCurve z.1 0 z.2) = 1 ↔ tau z.1 = z.2)) ∧
      ContDiffAt ℝ 1 (fun y => normalizedMaxCurve y 0 (tau y)) (referenceEntryState k) ∧
      HasFDerivAt (fun y => normalizedMaxCurve y 0 (tau y))
        (normalizedEventDifferential projectiveActiveWall (referenceEntryState k) 0
          (referenceNormalizedTime k)) (referenceEntryState k) := by
  have he := (referenceEntryState_crossing hk).2
  have hg : ContDiffAt ℝ 1 projectiveActiveWall
      (normalizedMaxCurve (referenceEntryState k) 0 (referenceNormalizedTime k)) := by
    rw [he]
    exact contDiffAt_projectiveActiveWall 1 (ne_of_gt (referenceExitState_clock_pos k))
  have hr : normalizedEventRate projectiveActiveWall (referenceEntryState k) 0
      (referenceNormalizedTime k) ≠ 0 := by
    unfold normalizedEventRate
    rw [he]
    exact ne_of_lt (referenceExitState_rate_neg hk)
  have hv : projectiveActiveWall
      (normalizedMaxCurve (referenceEntryState k) 0 (referenceNormalizedTime k)) = 1 := by
    rw [he]
    unfold projectiveActiveWall
    rw [referenceExitState_projective, referencePulse_exit hk]
    rfl
  obtain ⟨tau, hinit, hreg, hdt, hhit, huniq, hmap, hdmap⟩ :=
    exists_normalized_event (referenceEntryState_crossing hk).1 hg hr
  exact ⟨tau, hinit, hreg, hdt, by simpa only [hv] using hhit,
    by simpa only [hv] using huniq, hmap, hdmap⟩

theorem projective_event_differential {x : NormalizedState} {t₀ t : ℝ}
    (hA : 1 + normalizedMaxCurve x t₀ t 0 ≠ 0)
    (hc : stateConstraint (normalizedMaxCurve x t₀ t) = 1)
    (hv : projectiveField (toProjectiveState (normalizedMaxCurve x t₀ t)) 2 ≠ 0)
    (v : NormalizedState) :
    let y := normalizedMaxCurve x t₀ t
    let xi := fderiv ℝ toProjectiveState y (normalizedFlowDifferential x t₀ t v)
    fderiv ℝ toProjectiveState y (normalizedEventDifferential projectiveActiveWall x t₀ t v) =
      xi - (xi 2 / projectiveField (toProjectiveState y) 2) • projectiveField (toProjectiveState y) := by
  dsimp only
  change fderiv ℝ toProjectiveState (normalizedMaxCurve x t₀ t)
    (normalizedFlowDifferential x t₀ t v +
      (-(fderiv ℝ projectiveActiveWall (normalizedMaxCurve x t₀ t)
        (normalizedField (normalizedMaxCurve x t₀ t)))⁻¹ *
          fderiv ℝ projectiveActiveWall (normalizedMaxCurve x t₀ t)
            (normalizedFlowDifferential x t₀ t v)) • normalizedField (normalizedMaxCurve x t₀ t)) = _
  rw [map_add, map_smul]
  rw [projectiveActiveWall_fderiv_field hA hc,
    projectiveActiveWall_fderiv hA, toProjectiveState_fderiv_field hA hc]
  ext i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  field_simp
  ring

theorem referenceCore_event_differential {k : ℝ} (hk : 1 < k) (v : NormalizedState) :
    fderiv ℝ toProjectiveState (referenceExitState k)
      (normalizedEventDifferential projectiveActiveWall (referenceEntryState k) 0
        (referenceNormalizedTime k) v) =
      referenceExitProjection k (fderiv ℝ toProjectiveState (referenceExitState k)
        (normalizedFlowDifferential (referenceEntryState k) 0 (referenceNormalizedTime k) v)) := by
  have he := (referenceEntryState_crossing hk).2
  have hA : 1 + normalizedMaxCurve (referenceEntryState k) 0 (referenceNormalizedTime k) 0 ≠ 0 := by
    rw [he]
    exact ne_of_gt (referenceExitState_clock_pos k)
  have hc : stateConstraint (normalizedMaxCurve (referenceEntryState k) 0 (referenceNormalizedTime k)) = 1 := by
    rw [he]
    exact referenceExitState_constraint k
  have hv : projectiveField (toProjectiveState
      (normalizedMaxCurve (referenceEntryState k) 0 (referenceNormalizedTime k))) 2 ≠ 0 := by
    rw [he, referenceExitState_projective, referencePulse_exit_field hk]
    exact neg_ne_zero.mpr (ne_of_gt (referenceCoreGap_pos hk))
  have H := projective_event_differential hA hc hv v
  dsimp only at H
  rw [he, referenceExitState_projective] at H
  rw [referenceExitProjection_eq hk]
  exact H

end BianchiIX
