import BianchiIX.Analysis.ConnectionCoefficientMatrix
import BianchiIX.Dynamics.MatchingPhase
import BianchiIX.Dynamics.ConnectionLogRates

noncomputable section

namespace BianchiIX

theorem hasDerivAt_connectionLog_system {Y : ℝ → ProjectiveState} {t : ℝ}
    (hY : HasDerivAt Y (connectionLogField (Y t)) t) (hm : 1 < -Y t 0)
    (hD : connectionClockRate (Y t) ≠ 0) (hu : Y t 1 ≠ 0) (hv : Y t 2 ≠ 0) :
    HasDerivAt (fun s => (![matchingPhase (-Y s 0) (Y s 2) (Y s 3),
      Real.log (Y s 1), Real.log (Y s 2)] : Fin 3 → ℝ))
      (connectionLogRates (-Y t 0) (Y t 1) (Y t 2) (Y t 3)) t := by
  have hG := hasDerivAt_matchingPhase_connectionLog hY hm
  have hab := hasDerivAt_connectionLog_amplitudes hY hD hu hv
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · exact hG
  · exact hab.1
  · exact hab.2

end BianchiIX
