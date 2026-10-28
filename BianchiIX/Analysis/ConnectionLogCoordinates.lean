import BianchiIX.Dynamics.ConnectionLogSystem

noncomputable section

namespace BianchiIX

def connectionLogCoordinates (y : ProjectiveState) : Fin 4 → ℝ :=
  ![matchingPhase (-y 0) (y 2) (y 3), Real.log (y 1), Real.log (y 2), Real.log (y 3)]

def connectionLogTangent (y v : ProjectiveState) : Fin 4 → ℝ :=
  ![matchingPhaseSlope (-y 0) (y 2) (y 3) * (-v 0) +
      y 2 / phaseNorm (-y 0 + 1) (y 2) * v 2 + y 3 / phaseNorm (-y 0 - 1) (y 3) * v 3,
    v 1 / y 1, v 2 / y 2, v 3 / y 3]

def connectionLogCoordinateRates (y : ProjectiveState) : Fin 4 → ℝ :=
  ![connectionPhaseG (-y 0) (y 1) (y 2) (y 3),
    connectionStrongClockRate (-y 0) (y 1) (y 2) (y 3),
    connectionWeakClockRate (-y 0) (y 1) (y 2) (y 3), 1]

theorem contDiffAt_connectionLogCoordinates (n : WithTop ℕ∞) {y : ProjectiveState}
    (hm : 1 < -y 0) (hu : y 1 ≠ 0) (hv : y 2 ≠ 0) (hw : y 3 ≠ 0) :
    ContDiffAt ℝ n connectionLogCoordinates y := by
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i
  · exact contDiffAt_matchingPhase_comp n (by fun_prop) (by fun_prop) (by fun_prop) hm
  · exact (contDiff_apply ℝ ℝ 1).contDiffAt.log hu
  · exact (contDiff_apply ℝ ℝ 2).contDiffAt.log hv
  · exact (contDiff_apply ℝ ℝ 3).contDiffAt.log hw

theorem hasDerivAt_connectionLogCoordinates {Y : ℝ → ProjectiveState} {v : ProjectiveState} {t : ℝ}
    (hY : HasDerivAt Y v t) (hm : 1 < -Y t 0) (hu : Y t 1 ≠ 0) (hv : Y t 2 ≠ 0) (hw : Y t 3 ≠ 0) :
    HasDerivAt (fun s => connectionLogCoordinates (Y s)) (connectionLogTangent (Y t) v) t := by
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · exact hasDerivAt_matchingPhase (hasDerivAt_pi.mp hY 0).neg
      (hasDerivAt_pi.mp hY 2) (hasDerivAt_pi.mp hY 3) hm
  · exact (hasDerivAt_pi.mp hY 1).log hu
  · exact (hasDerivAt_pi.mp hY 2).log hv
  · exact (hasDerivAt_pi.mp hY 3).log hw

theorem connectionLogCoordinates_fderiv {y : ProjectiveState}
    (hm : 1 < -y 0) (hu : y 1 ≠ 0) (hv : y 2 ≠ 0) (hw : y 3 ≠ 0) (v : ProjectiveState) :
    fderiv ℝ connectionLogCoordinates y v = connectionLogTangent y v := by
  have hline : HasDerivAt (fun s : ℝ => y + s • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add y
  have hd : HasFDerivAt connectionLogCoordinates (fderiv ℝ connectionLogCoordinates y) (y + (0 : ℝ) • v) := by
    simpa using ((contDiffAt_connectionLogCoordinates 1 hm hu hv hw).differentiableAt (by norm_num)).hasFDerivAt
  have H := hasDerivAt_connectionLogCoordinates hline (by simpa using hm)
    (by simpa using hu) (by simpa using hv) (by simpa using hw)
  have HD : HasDerivAt (fun s : ℝ => connectionLogCoordinates (y + s • v))
      (fderiv ℝ connectionLogCoordinates y v) 0 := by
    simpa only [Function.comp_def] using hd.comp_hasDerivAt 0 hline
  simpa only [zero_smul, add_zero] using HD.unique H

theorem hasDerivAt_connectionLogCoordinates_flow {Y : ℝ → ProjectiveState} {t : ℝ}
    (hY : HasDerivAt Y (connectionLogField (Y t)) t) (hm : 1 < -Y t 0)
    (hD : connectionClockRate (Y t) ≠ 0) (hu : Y t 1 ≠ 0) (hv : Y t 2 ≠ 0) (hw : Y t 3 ≠ 0) :
    HasDerivAt (fun s => connectionLogCoordinates (Y s)) (connectionLogCoordinateRates (Y t)) t := by
  have H := hasDerivAt_connectionLog_system hY hm hD hu hv
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · exact hasDerivAt_pi.mp H 0
  · exact hasDerivAt_pi.mp H 1
  · exact hasDerivAt_pi.mp H 2
  · apply ((hasDerivAt_pi.mp hY 3).log hw).congr_deriv
    rw [(connectionLogField_components hD).2.2.2, div_self hw]
    rfl

theorem connectionLogCoordinates_fderiv_field {y : ProjectiveState}
    (hm : 1 < -y 0) (hD : connectionClockRate y ≠ 0) (hu : y 1 ≠ 0) (hv : y 2 ≠ 0) (hw : y 3 ≠ 0) :
    fderiv ℝ connectionLogCoordinates y (connectionLogField y) = connectionLogCoordinateRates y := by
  have hline : HasDerivAt (fun s : ℝ => y + s • connectionLogField y) (connectionLogField y) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (connectionLogField y)).const_add y
  have hY : HasDerivAt (fun s : ℝ => y + s • connectionLogField y)
      (connectionLogField (y + (0 : ℝ) • connectionLogField y)) 0 := by simpa using hline
  have H1 := hasDerivAt_connectionLogCoordinates hY (by simpa using hm)
    (by simpa using hu) (by simpa using hv) (by simpa using hw)
  have H2 := hasDerivAt_connectionLogCoordinates_flow hY (by simpa using hm) (by simpa using hD)
    (by simpa using hu) (by simpa using hv) (by simpa using hw)
  rw [connectionLogCoordinates_fderiv hm hu hv hw]
  simpa only [zero_smul, add_zero] using H1.unique H2

end BianchiIX
