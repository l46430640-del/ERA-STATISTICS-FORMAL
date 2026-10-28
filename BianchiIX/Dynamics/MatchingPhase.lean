import BianchiIX.Algebra.MatchingPhaseBounds
import BianchiIX.Dynamics.ConnectionClock

noncomputable section

namespace BianchiIX

theorem hasDerivAt_matchingPhase_scaled {Y : ℝ → ProjectiveState} {a t : ℝ}
    (hY : HasDerivAt Y (a • projectiveField (Y t)) t) (hm : 1 < -Y t 0) :
    HasDerivAt (fun s => matchingPhase (-Y s 0) (Y s 2) (Y s 3))
      (a * matchingPhaseRate (-Y t 0) (Y t 1) (Y t 2) (Y t 3)) t := by
  have H := hasDerivAt_matchingPhase (hasDerivAt_pi.mp hY 0).neg
    (hasDerivAt_pi.mp hY 2) (hasDerivAt_pi.mp hY 3) hm
  simp only [Pi.neg_apply] at H
  have hrate := matchingPhase_directional (u := Y t 1) (v := Y t 2) (w := Y t 3) hm
  simp only [neg_neg] at hrate
  convert! H using 1
  rw [← hrate]
  change a * _ = matchingPhaseSlope _ _ _ * (-(a * phaseVelocity _ _ _ _)) +
    _ * (a * activeVelocity _ _ _ _) + _ * (a * weakVelocity _ _ _ _)
  ring

theorem hasDerivAt_matchingPhase_connectionLog {Y : ℝ → ProjectiveState} {t : ℝ}
    (hY : HasDerivAt Y (connectionLogField (Y t)) t) (hm : 1 < -Y t 0) :
    HasDerivAt (fun s => matchingPhase (-Y s 0) (Y s 2) (Y s 3))
      (matchingPhaseRate (-Y t 0) (Y t 1) (Y t 2) (Y t 3) / connectionClockRate (Y t)) t := by
  convert! hasDerivAt_matchingPhase_scaled hY hm using 1
  ring

end BianchiIX
