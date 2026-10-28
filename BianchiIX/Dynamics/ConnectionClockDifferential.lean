import BianchiIX.Dynamics.ConnectionClock
import BianchiIX.Dynamics.ProjectiveOriginalTime
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

noncomputable section

namespace BianchiIX

def connectionLogClock (y : ProjectiveState) : ℝ := Real.log (y 3)

def connectionOriginalClockRate (y : ProjectiveState) : ℝ :=
  (6 / projectiveStateDenom y) * connectionClockRate y

theorem contDiffAt_connectionLogClock (n : WithTop ℕ∞) {y : ProjectiveState}
    (hw : y 3 ≠ 0) : ContDiffAt ℝ n connectionLogClock y :=
  (contDiff_apply ℝ ℝ 3).contDiffAt.log hw

theorem contDiffAt_connectionOriginalClockRate (n : WithTop ℕ∞) {y : ProjectiveState}
    (hD : projectiveStateDenom y ≠ 0) : ContDiffAt ℝ n connectionOriginalClockRate y := by
  unfold connectionOriginalClockRate
  exact (contDiffAt_const.div (contDiff_projectiveStateDenom n).contDiffAt hD).mul
    (contDiff_connectionClockRate n).contDiffAt

theorem connectionLogClock_fderiv {y : ProjectiveState} (hw : y 3 ≠ 0) (v : ProjectiveState) :
    fderiv ℝ connectionLogClock y v = v 3 / y 3 := by
  have H := ((hasFDerivAt_apply (𝕜 := ℝ) (3 : Fin 4) y).log hw)
  rw [show fderiv ℝ connectionLogClock y = _ from H.fderiv]
  simp only [smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
  ring

theorem connectionLogClock_fderiv_field {y : ProjectiveState} (hw : y 3 ≠ 0) :
    fderiv ℝ connectionLogClock y (projectiveOriginalField y) = connectionOriginalClockRate y := by
  rw [connectionLogClock_fderiv hw]
  change (6 / projectiveStateDenom y * weakVelocity (y 0) (y 1) (y 2) (y 3)) / y 3 = _
  dsimp [connectionOriginalClockRate, connectionClockRate, connectionSpeed, weakVelocity]
  field_simp

theorem projectiveOriginalField_connectionLog {y : ProjectiveState} (hD : connectionClockRate y ≠ 0) :
    projectiveOriginalField y = connectionOriginalClockRate y • connectionLogField y := by
  unfold connectionOriginalClockRate connectionLogField projectiveOriginalField
  rw [smul_smul, mul_assoc, mul_inv_cancel₀ hD, mul_one]

end BianchiIX
