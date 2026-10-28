import BianchiIX.Dynamics.EntranceRegion
import BianchiIX.Dynamics.ProjectiveOriginalTime
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

noncomputable section

namespace BianchiIX

def entranceLogField (y : ProjectiveState) : ProjectiveState :=
  (entranceClockRate y)⁻¹ • projectiveField y

def entranceLogClock (y : ProjectiveState) : ℝ := Real.log (y 2)

def entranceOriginalClockRate (y : ProjectiveState) : ℝ :=
  (6 / projectiveStateDenom y) * entranceClockRate y

theorem contDiff_entranceClockRate (n : WithTop ℕ∞) : ContDiff ℝ n entranceClockRate := by
  unfold entranceClockRate connectionSpeed coupling
  fun_prop

theorem contDiffAt_entranceLogField (n : WithTop ℕ∞) {y : ProjectiveState}
    (hD : entranceClockRate y ≠ 0) : ContDiffAt ℝ n entranceLogField y :=
  ((contDiff_entranceClockRate n).contDiffAt.inv hD).smul
    (contDiff_projectiveField n).contDiffAt

theorem entranceLogField_active {y : ProjectiveState} (hD : entranceClockRate y ≠ 0) :
    entranceLogField y 2 = y 2 := by
  change (entranceClockRate y)⁻¹ * (entranceClockRate y * y 2) = y 2
  rw [← mul_assoc, inv_mul_cancel₀ hD, one_mul]

theorem contDiffAt_entranceLogClock (n : WithTop ℕ∞) {y : ProjectiveState}
    (hv : y 2 ≠ 0) : ContDiffAt ℝ n entranceLogClock y :=
  (contDiff_apply ℝ ℝ 2).contDiffAt.log hv

theorem contDiffAt_entranceOriginalClockRate (n : WithTop ℕ∞) {y : ProjectiveState}
    (hD : projectiveStateDenom y ≠ 0) : ContDiffAt ℝ n entranceOriginalClockRate y := by
  unfold entranceOriginalClockRate
  exact (contDiffAt_const.div (contDiff_projectiveStateDenom n).contDiffAt hD).mul
    (contDiff_entranceClockRate n).contDiffAt

theorem entranceLogClock_fderiv {y : ProjectiveState} (hv : y 2 ≠ 0) (v : ProjectiveState) :
    fderiv ℝ entranceLogClock y v = v 2 / y 2 := by
  have H := (hasFDerivAt_apply (𝕜 := ℝ) (2 : Fin 4) y).log hv
  rw [show fderiv ℝ entranceLogClock y = _ from H.fderiv]
  simp only [smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
  ring

theorem entranceLogClock_fderiv_field {y : ProjectiveState} (hv : y 2 ≠ 0) :
    fderiv ℝ entranceLogClock y (projectiveOriginalField y) = entranceOriginalClockRate y := by
  rw [entranceLogClock_fderiv hv]
  change (6 / projectiveStateDenom y * activeVelocity (y 0) (y 1) (y 2) (y 3)) / y 2 = _
  dsimp [entranceOriginalClockRate, entranceClockRate, connectionSpeed, activeVelocity]
  field_simp

theorem projectiveOriginalField_entranceLog {y : ProjectiveState} (hD : entranceClockRate y ≠ 0) :
    projectiveOriginalField y = entranceOriginalClockRate y • entranceLogField y := by
  unfold entranceOriginalClockRate entranceLogField projectiveOriginalField
  rw [smul_smul, mul_assoc, mul_inv_cancel₀ hD, mul_one]

end BianchiIX
