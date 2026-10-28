import BianchiIX.Dynamics.ExitFlowVariation
import BianchiIX.Dynamics.ExitTailVariationScale

noncomputable section

namespace BianchiIX

theorem exitOriginalClockRate_normalized {y : ProjectiveState} {t₀ t : ℝ}
    (hD : 0 < projectiveStateDenom y) (ht : t ∈ normalizedMaxDomain (fromProjectiveState y) t₀)
    (hA : 0 < 1 + normalizedMaxCurve (fromProjectiveState y) t₀ t 0) :
    exitOriginalClockRate (projectiveOriginalFlow y t₀ t) =
      (1 + normalizedMaxCurve (fromProjectiveState y) t₀ t 0) *
        exitClockRate (projectiveOriginalFlow y t₀ t) := by
  have hc : stateConstraint (normalizedMaxCurve (fromProjectiveState y) t₀ t) = 1 :=
    (normalizedMaxCurve_constraint ht).trans (fromProjectiveState_constraint hD.ne')
  unfold exitOriginalClockRate
  rw [show 6 / projectiveStateDenom (projectiveOriginalFlow y t₀ t) =
    1 + normalizedMaxCurve (fromProjectiveState y) t₀ t 0 from projective_inverse_scale hA.ne' hc]

/-- Reparametrizing the actual projected tangent removes the original-time clock factor exactly. -/
theorem hasDerivAt_exitProjectedFlowVariation_clock {y : ProjectiveState} {t₀ s : ℝ} {τ : ℝ → ℝ}
    (hD : 0 < projectiveStateDenom y) (ht : τ s ∈ normalizedMaxDomain (fromProjectiveState y) t₀)
    (hA : 0 < 1 + normalizedMaxCurve (fromProjectiveState y) t₀ (τ s) 0)
    (hV : 0 < projectiveOriginalFlow y t₀ (τ s) 2)
    (hm : projectiveOriginalFlow y t₀ (τ s) 0 < 1)
    (hd : exitClockRate (projectiveOriginalFlow y t₀ (τ s)) ≠ 0)
    (hτ : HasDerivAt τ (1 / exitOriginalClockRate (projectiveOriginalFlow y t₀ (τ s))) s)
    (w : ProjectiveState) :
    HasDerivAt (fun r => exitProjectedFlowVariation y t₀ (τ r) w)
      (fderiv ℝ (exitTailField (projectiveOriginalFlow y t₀ (τ s) 2))
        (toExitTailState (projectiveOriginalFlow y t₀ (τ s)))
          (exitProjectedFlowVariation y t₀ (τ s) w)) s := by
  have hr : exitOriginalClockRate (projectiveOriginalFlow y t₀ (τ s)) ≠ 0 := by
    rw [exitOriginalClockRate_normalized hD ht hA]
    exact mul_ne_zero hA.ne' hd
  have H := (hasDerivAt_exitProjectedFlowVariation hD ht hA hV hm hd w).scomp s hτ
  simpa only [Function.comp_def, smul_smul, one_div, inv_mul_cancel₀ hr, one_smul] using H

end BianchiIX
