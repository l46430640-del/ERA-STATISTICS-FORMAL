import BianchiIX.Analysis.CompactIntegralRegularity
import BianchiIX.Dynamics.CoreLogDerivative

noncomputable section

namespace BianchiIX

open Set MeasureTheory

/-- Joint regularity along the actual core gives an open-neighborhood extension through zero walls. -/
theorem contDiffAt_log_coreReturnMultiplier {Y : CoreAngleState} {τ : CoreAngleState → ℝ}
    (hk : 6 ≤ Y 0) (hD : 0 < projectiveStateDenom (coreRadiusEntry Y))
    (hτ : ContDiffAt ℝ 1 τ Y) (hpos : 0 ≤ τ Y)
    (hdom : Icc 0 (τ Y) ⊆ normalizedMaxDomain (fromProjectiveState (coreRadiusEntry Y)) 0)
    (hA : ∀ t ∈ Icc 0 (τ Y), 0 < 1 + normalizedMaxCurve (fromProjectiveState (coreRadiusEntry Y)) 0 t 0)
    (hcore : ∀ t ∈ Icc 0 (τ Y), coreRegion (Y 0) (projectiveOriginalFlow (coreRadiusEntry Y) 0 t))
    (i : Fin 2) : ContDiffAt ℝ 1 (fun Z => Real.log (coreReturnMultiplier τ Z i)) Y := by
  have hF (t : ℝ) (ht : t ∈ Icc 0 (τ Y)) := contDiffAt_pi.mp
    (contDiffAt_coreEntryLogRates (by linarith only [hk]) hD (hdom ht) (hA t ht)
      (lt_of_lt_of_le zero_lt_one (hcore t ht).2.1)
      (ne_of_gt (coreRegion_clock_regular hk (hcore t ht)).1)
      (ne_of_gt (coreRegion_clock_regular hk (hcore t ht)).2.1)) i
  convert! contDiffAt_moving_intervalIntegral_of_contDiffAt hτ hpos hF using 1
  ext Z
  exact log_coreFlowMultiplier _ _ _ _ _

theorem contDiffAt_coreReturnMultiplier {Y : CoreAngleState} {τ : CoreAngleState → ℝ}
    (hk : 6 ≤ Y 0) (hD : 0 < projectiveStateDenom (coreRadiusEntry Y))
    (hτ : ContDiffAt ℝ 1 τ Y) (hpos : 0 ≤ τ Y)
    (hdom : Icc 0 (τ Y) ⊆ normalizedMaxDomain (fromProjectiveState (coreRadiusEntry Y)) 0)
    (hA : ∀ t ∈ Icc 0 (τ Y), 0 < 1 + normalizedMaxCurve (fromProjectiveState (coreRadiusEntry Y)) 0 t 0)
    (hcore : ∀ t ∈ Icc 0 (τ Y), coreRegion (Y 0) (projectiveOriginalFlow (coreRadiusEntry Y) 0 t))
    (i : Fin 2) : ContDiffAt ℝ 1 (fun Z => coreReturnMultiplier τ Z i) Y := by
  convert! (contDiffAt_log_coreReturnMultiplier hk hD hτ hpos hdom hA hcore i).exp using 1
  ext Z
  exact (Real.exp_log (coreFlowMultiplier_pos _ _ _ _ i)).symm

end BianchiIX
