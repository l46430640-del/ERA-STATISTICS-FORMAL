import BianchiIX.Analysis.ConnectionLogCoordinates
import BianchiIX.Analysis.ClockVariation

noncomputable section

namespace BianchiIX

open Filter
open scoped Topology

def connectionLogLinearizedRates (y : ProjectiveState) (d : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![∑ j : Fin 4, connectionLogCoefficientMatrix (-y 0) (y 1) (y 2) (y 3) 0 j * d j,
    ∑ j : Fin 4, connectionLogCoefficientMatrix (-y 0) (y 1) (y 2) (y 3) 1 j * d j,
    ∑ j : Fin 4, connectionLogCoefficientMatrix (-y 0) (y 1) (y 2) (y 3) 2 j * d j, 0]

theorem connectionLog_regular_near {y : ProjectiveState}
    (hm : 1 < -y 0) (hD : connectionClockRate y ≠ 0) (hu : y 1 ≠ 0) (hv : y 2 ≠ 0) (hw : y 3 ≠ 0) :
    ∀ᶠ z : ProjectiveState in 𝓝 y,
      1 < -z 0 ∧ connectionClockRate z ≠ 0 ∧ z 1 ≠ 0 ∧ z 2 ≠ 0 ∧ z 3 ≠ 0 := by
  filter_upwards [(continuous_apply 0).neg.continuousAt.eventually (isOpen_Ioi.mem_nhds hm),
    (contDiff_connectionClockRate 1).continuous.continuousAt.eventually_ne hD,
    (continuous_apply 1).continuousAt.eventually_ne hu,
    (continuous_apply 2).continuousAt.eventually_ne hv,
    (continuous_apply 3).continuousAt.eventually_ne hw] with z hmz hDz huz hvz hwz
  exact ⟨hmz, hDz, huz, hvz, hwz⟩

theorem connectionLogCoordinates_lie_eventuallyEq {y : ProjectiveState}
    (hm : 1 < -y 0) (hD : connectionClockRate y ≠ 0) (hu : y 1 ≠ 0) (hv : y 2 ≠ 0) (hw : y 3 ≠ 0) :
    (fun z => fderiv ℝ connectionLogCoordinates z (connectionLogField z)) =ᶠ[𝓝 y]
      connectionLogCoordinateRates := by
  filter_upwards [connectionLog_regular_near hm hD hu hv hw] with z hz
  exact connectionLogCoordinates_fderiv_field hz.1 hz.2.1 hz.2.2.1 hz.2.2.2.1 hz.2.2.2.2

theorem hasDerivAt_connectionLogCoordinateRates {Y : ℝ → ProjectiveState} {v : ProjectiveState} {t : ℝ}
    (hY : HasDerivAt Y v t) (hm : 1 < -Y t 0) (hD : connectionClockRate (Y t) ≠ 0)
    (hf : matchingPhaseSlope (-Y t 0) (Y t 2) (Y t 3) ≠ 0)
    (hu : Y t 1 ≠ 0) (hv : Y t 2 ≠ 0) (hw : Y t 3 ≠ 0) :
    HasDerivAt (fun s => connectionLogCoordinateRates (Y s))
      (connectionLogLinearizedRates (Y t) (connectionLogTangent (Y t) v)) t := by
  let d := connectionLogTangent (Y t) v
  have hm' : HasDerivAt (fun s => -Y s 0)
      (d 0 / matchingPhaseSlope (-Y t 0) (Y t 2) (Y t 3) +
        matchingPhaseVVariation (-Y t 0) (Y t 2) (Y t 3) * d 2 +
        matchingPhaseWVariation (-Y t 0) (Y t 2) (Y t 3) * d 3) t := by
    apply (hasDerivAt_pi.mp hY 0).neg.congr_deriv
    dsimp [d, connectionLogTangent, matchingPhaseVVariation, matchingPhaseWVariation]
    generalize hF : matchingPhaseSlope (-Y t 0) (Y t 2) (Y t 3) = F at hf ⊢
    generalize hK : phaseNorm (-Y t 0 + 1) (Y t 2) = K
    generalize hL : phaseNorm (-Y t 0 - 1) (Y t 3) = L
    field_simp
    ring
  have hwall (i : Fin 4) (hi : Y t i ≠ 0) : HasDerivAt (fun s => Y s i) (Y t i * (v i / Y t i)) t := by
    simpa only [mul_div_cancel₀ _ hi] using hasDerivAt_pi.mp hY i
  have H := hasDerivAt_connectionLogRates_weighted
    (m := fun s => -Y s 0) (u := fun s => Y s 1) (v := fun s => Y s 2) (w := fun s => Y s 3)
    (t := t) d hm' (hwall 1 hu) (hwall 2 hv) (hwall 3 hw) hm hf hD
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · exact hasDerivAt_pi.mp H 0
  · exact hasDerivAt_pi.mp H 1
  · exact hasDerivAt_pi.mp H 2
  · exact hasDerivAt_const t (1 : ℝ)

theorem connectionLogCoordinateRates_fderiv {y : ProjectiveState}
    (hm : 1 < -y 0) (hD : connectionClockRate y ≠ 0)
    (hf : matchingPhaseSlope (-y 0) (y 2) (y 3) ≠ 0)
    (hu : y 1 ≠ 0) (hv : y 2 ≠ 0) (hw : y 3 ≠ 0) (v : ProjectiveState) :
    fderiv ℝ connectionLogCoordinateRates y v = connectionLogLinearizedRates y (connectionLogTangent y v) := by
  have hC := contDiffAt_connectionLogCoordinates 2 hm hu hv hw
  have hCD := (hC.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hF := (contDiffAt_connectionLogField 1 hD).differentiableAt (by norm_num)
  have hR := (hCD.hasFDerivAt.clm_apply hF.hasFDerivAt).congr_of_eventuallyEq
    (connectionLogCoordinates_lie_eventuallyEq hm hD hu hv hw).symm
  have hline : HasDerivAt (fun s : ℝ => y + s • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add y
  have hd : HasFDerivAt connectionLogCoordinateRates (fderiv ℝ connectionLogCoordinateRates y)
      (y + (0 : ℝ) • v) := by simpa using hR.differentiableAt.hasFDerivAt
  have HD : HasDerivAt (fun s : ℝ => connectionLogCoordinateRates (y + s • v))
      (fderiv ℝ connectionLogCoordinateRates y v) 0 := by
    simpa only [Function.comp_def] using hd.comp_hasDerivAt 0 hline
  have H := hasDerivAt_connectionLogCoordinateRates hline (by simpa using hm) (by simpa using hD)
    (by simpa using hf) (by simpa using hu) (by simpa using hv) (by simpa using hw)
  simpa only [zero_smul, add_zero] using HD.unique H

/-- The coordinate tangent of an actual variational solution obeys the four-column system. -/
theorem hasDerivAt_connectionLogTangent {Y v : ℝ → ProjectiveState} {t : ℝ}
    (hY : HasDerivAt Y (connectionLogField (Y t)) t)
    (hv' : HasDerivAt v (fderiv ℝ connectionLogField (Y t) (v t)) t)
    (hm : 1 < -Y t 0) (hD : connectionClockRate (Y t) ≠ 0)
    (hf : matchingPhaseSlope (-Y t 0) (Y t 2) (Y t 3) ≠ 0)
    (hu : Y t 1 ≠ 0) (hv : Y t 2 ≠ 0) (hw : Y t 3 ≠ 0) :
    HasDerivAt (fun s => connectionLogTangent (Y s) (v s))
      (connectionLogLinearizedRates (Y t) (connectionLogTangent (Y t) (v t))) t := by
  have H := hasDerivAt_observable_variation (contDiffAt_connectionLogCoordinates 2 hm hu hv hw)
    ((contDiffAt_connectionLogField 1 hD).differentiableAt (by norm_num)) hY hv'
  rw [(connectionLogCoordinates_lie_eventuallyEq hm hD hu hv hw).fderiv_eq,
    connectionLogCoordinateRates_fderiv hm hD hf hu hv hw] at H
  apply H.congr_of_eventuallyEq
  filter_upwards [hY.continuousAt.eventually (connectionLog_regular_near hm hD hu hv hw)] with s hs
  exact (connectionLogCoordinates_fderiv hs.1 hs.2.2.1 hs.2.2.2.1 hs.2.2.2.2 (v s)).symm

end BianchiIX
