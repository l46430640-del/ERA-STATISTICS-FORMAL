import BianchiIX.Analysis.ConnectionGrowingSources

noncomputable section

namespace BianchiIX

theorem continuousAt_connectionStrongWallColumn {Y : ℝ → ProjectiveState} {t : ℝ}
    (hc : ContinuousAt Y t) (hm : 1 < -Y t 0)
    (hD : connectionSpeed (-Y t 0) (Y t 1) (Y t 2) (Y t 3) ≠ 0)
    (hf : matchingPhaseSlope (-Y t 0) (Y t 2) (Y t 3) ≠ 0) :
    ContinuousAt (fun s => connectionStrongClockPartials (-Y s 0) (Y s 1) (Y s 2) (Y s 3) 3) t := by
  have hcoord (i : Fin 4) : ContinuousAt (fun s => Y s i) t := (continuous_apply i).continuousAt.comp hc
  have hKp : phaseNorm (-Y t 0 + 1) (Y t 2) ≠ 0 := ne_of_gt (phaseNorm_pos (by linarith only [hm]))
  have hKm : phaseNorm (-Y t 0 - 1) (Y t 3) ≠ 0 := ne_of_gt (phaseNorm_pos (by linarith only [hm]))
  have hcKp : ContinuousAt (fun s => phaseNorm (-Y s 0 + 1) (Y s 2)) t := by unfold phaseNorm; fun_prop
  have hcKm : ContinuousAt (fun s => phaseNorm (-Y s 0 - 1) (Y s 3)) t := by unfold phaseNorm; fun_prop
  have hcf : ContinuousAt (fun s => matchingPhaseSlope (-Y s 0) (Y s 2) (Y s 3)) t := by
    unfold matchingPhaseSlope
    fun_prop
  have hcD : ContinuousAt (fun s => connectionSpeed (-Y s 0) (Y s 1) (Y s 2) (Y s 3)) t := by
    unfold connectionSpeed coupling
    fun_prop
  have hca : ContinuousAt (fun s => connectionStrongClockRate (-Y s 0) (Y s 1) (Y s 2) (Y s 3)) t := by
    unfold connectionStrongClockRate connectionStrongRate
    fun_prop
  have hcW : ContinuousAt (fun s => matchingPhaseWVariation (-Y s 0) (Y s 2) (Y s 3)) t := by
    unfold matchingPhaseWVariation
    exact ((hcoord 3).pow 2).neg.div (hcKm.mul hcf) (mul_ne_zero hKm hf)
  change ContinuousAt (fun s =>
    (-(-Y s 0 + connectionStrongClockRate (-Y s 0) (Y s 1) (Y s 2) (Y s 3)) *
      matchingPhaseWVariation (-Y s 0) (Y s 2) (Y s 3) + Y s 3 * (Y s 2 - Y s 3) +
      connectionStrongClockRate (-Y s 0) (Y s 1) (Y s 2) (Y s 3) * Y s 1 * Y s 3) /
      connectionSpeed (-Y s 0) (Y s 1) (Y s 2) (Y s 3)) t
  fun_prop

end BianchiIX
