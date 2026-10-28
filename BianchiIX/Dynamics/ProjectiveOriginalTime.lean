import BianchiIX.Dynamics.ProjectiveRegularity
import BianchiIX.Dynamics.ReferenceScattering

noncomputable section

namespace BianchiIX

def projectiveOriginalField (y : ProjectiveState) : ProjectiveState :=
  (6 / projectiveStateDenom y) • projectiveField y

theorem contDiffAt_projectiveOriginalField (n : WithTop ℕ∞) {y : ProjectiveState}
    (hD : projectiveStateDenom y ≠ 0) : ContDiffAt ℝ n projectiveOriginalField y := by
  have hd := (contDiff_projectiveStateDenom n).contDiffAt (x := y)
  have hf := (contDiff_projectiveField n).contDiffAt (x := y)
  unfold projectiveOriginalField
  fun_prop

theorem hasDerivAt_projectiveOriginalFlow {alpha : ℝ → NormalizedState} {t : ℝ}
    (hα : HasDerivAt alpha (normalizedField (alpha t)) t)
    (hA : 1 + alpha t 0 ≠ 0) (hc : stateConstraint (alpha t) = 1) :
    HasDerivAt (fun s => toProjectiveState (alpha s))
      (projectiveOriginalField (toProjectiveState (alpha t))) t := by
  have hs : 6 / projectiveStateDenom (toProjectiveState (alpha t)) = 1 + alpha t 0 :=
    projective_inverse_scale hA hc
  rw [projectiveOriginalField, hs]
  exact hasDerivAt_toProjectiveState_normalized hα hA hc

theorem hasFDerivAt_projectiveInverseScale {y : ProjectiveState}
    (hD : projectiveStateDenom y ≠ 0) :
    HasFDerivAt (fun z => 6 / projectiveStateDenom z)
      ((-6 / projectiveStateDenom y ^ 2) • fderiv ℝ projectiveStateDenom y) y := by
  have hd := ((contDiff_projectiveStateDenom 1).differentiable (by norm_num) y).hasFDerivAt
  have hs : HasDerivAt (fun s : ℝ => 6 / s) (-6 / projectiveStateDenom y ^ 2)
      (projectiveStateDenom y) := by
    convert! (hasDerivAt_const (projectiveStateDenom y) (6 : ℝ)).div
      (hasDerivAt_id (projectiveStateDenom y)) hD using 1
    simp
  exact hs.comp_hasFDerivAt y hd

theorem projectiveOriginalField_fderiv {y : ProjectiveState}
    (hD : projectiveStateDenom y ≠ 0) (xi : ProjectiveState) :
    fderiv ℝ projectiveOriginalField y xi =
      (6 / projectiveStateDenom y) • fderiv ℝ projectiveField y xi -
      (6 * fderiv ℝ projectiveStateDenom y xi / projectiveStateDenom y ^ 2) • projectiveField y := by
  have hf := ((contDiff_projectiveField 1).differentiable (by norm_num) y).hasFDerivAt
  have hd := (hasFDerivAt_projectiveInverseScale hD).smul hf
  rw [show fderiv ℝ projectiveOriginalField y = _ from hd.fderiv]
  ext i
  change 6 / projectiveStateDenom y * (fderiv ℝ projectiveField y xi) i +
    (-6 / projectiveStateDenom y ^ 2 * fderiv ℝ projectiveStateDenom y xi) * projectiveField y i = _
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem referenceOriginalVariation_identity (k t : ℝ) (xi : ProjectiveState) :
    (projectiveStateDenom (referencePulse k t) / 6) •
        fderiv ℝ projectiveOriginalField (referencePulse k t) xi =
      referenceVariationVelocity k t xi
        (-fderiv ℝ projectiveStateDenom (referencePulse k t) xi /
          projectiveStateDenom (referencePulse k t)) := by
  have hD := ne_of_gt (referencePulse_denom_pos k t)
  rw [projectiveOriginalField_fderiv hD]
  ext i
  dsimp [referenceVariationVelocity]
  field_simp
  ring

/-- Rescale an original-time variational solution using the reference clock. -/
theorem hasDerivAt_referenceOriginalVariation {k t : ℝ} {xi : ℝ → ProjectiveState}
    {clock : ℝ → ℝ}
    (hxi : HasDerivAt xi
      (fderiv ℝ projectiveOriginalField (referencePulse k t) (xi (clock t))) (clock t))
    (hc : HasDerivAt clock (projectiveStateDenom (referencePulse k t) / 6) t) :
    HasDerivAt (fun s => xi (clock s))
      (referenceVariationVelocity k t (xi (clock t))
        (-fderiv ℝ projectiveStateDenom (referencePulse k t) (xi (clock t)) /
          projectiveStateDenom (referencePulse k t))) t := by
  have H := hxi.scomp t hc
  rw [referenceOriginalVariation_identity] at H
  exact H

end BianchiIX
