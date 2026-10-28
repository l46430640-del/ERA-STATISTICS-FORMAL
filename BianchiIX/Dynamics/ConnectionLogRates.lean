import BianchiIX.Analysis.ConnectionAmplitudeCoordinates
import BianchiIX.Analysis.ConnectionAmplitudeBounds
import BianchiIX.Dynamics.ConnectionClock

noncomputable section

namespace BianchiIX

theorem connectionLogField_amplitude {y : ProjectiveState} (hD : connectionClockRate y ≠ 0) :
    connectionLogField y 1 = connectionStrongClockRate (-y 0) (y 1) (y 2) (y 3) * y 1 ∧
    connectionLogField y 2 = connectionWeakClockRate (-y 0) (y 1) (y 2) (y 3) * y 2 := by
  have H := connectionLogField_components hD
  have hb := (connection_clock_identities hD).1
  simp only [neg_neg] at hb
  refine ⟨H.2.1, ?_⟩
  rw [H.2.2.1]
  dsimp only [connectionClockRate, connectionWeakClockRate]
  rw [hb]

theorem hasDerivAt_connectionLog_amplitudes {Y : ℝ → ProjectiveState} {t : ℝ}
    (hY : HasDerivAt Y (connectionLogField (Y t)) t) (hD : connectionClockRate (Y t) ≠ 0)
    (hu : Y t 1 ≠ 0) (hv : Y t 2 ≠ 0) :
    HasDerivAt (fun s => Real.log (Y s 1)) (connectionStrongClockRate (-Y t 0) (Y t 1) (Y t 2) (Y t 3)) t ∧
    HasDerivAt (fun s => Real.log (Y s 2)) (connectionWeakClockRate (-Y t 0) (Y t 1) (Y t 2) (Y t 3)) t := by
  have H := connectionLogField_amplitude hD
  constructor
  · apply ((hasDerivAt_pi.mp hY 1).log hu).congr_deriv
    rw [H.1, mul_div_cancel_right₀ _ hu]
  · apply ((hasDerivAt_pi.mp hY 2).log hv).congr_deriv
    rw [H.2, mul_div_cancel_right₀ _ hv]

end BianchiIX
