import BianchiIX.Dynamics.ConnectionFlowVariation
import BianchiIX.Analysis.ConnectionLogLinearization
import BianchiIX.Dynamics.ConnectionExistence

noncomputable section

namespace BianchiIX

open Set

def connectionLogFlowVariation (y : ProjectiveState) (t₀ t : ℝ) (v : ProjectiveState) : Fin 4 → ℝ :=
  connectionLogTangent (projectiveOriginalFlow y t₀ t) (connectionProjectedFlowVariation y t₀ t v)

theorem hasDerivAt_projectiveOriginalFlow_connectionLog {y : ProjectiveState} {t₀ z : ℝ}
    {q : ℝ → ℝ} (hD : 0 < projectiveStateDenom y)
    (ht : q z ∈ normalizedMaxDomain (fromProjectiveState y) t₀)
    (hA : 0 < 1 + normalizedMaxCurve (fromProjectiveState y) t₀ (q z) 0)
    (hclock : connectionClockRate (projectiveOriginalFlow y t₀ (q z)) ≠ 0)
    (hq : HasDerivAt q (1 / connectionOriginalClockRate (projectiveOriginalFlow y t₀ (q z))) z) :
    HasDerivAt (fun r => projectiveOriginalFlow y t₀ (q r))
      (connectionLogField (projectiveOriginalFlow y t₀ (q z))) z := by
  have hc : stateConstraint (normalizedMaxCurve (fromProjectiveState y) t₀ (q z)) = 1 :=
    (normalizedMaxCurve_constraint ht).trans (fromProjectiveState_constraint (ne_of_gt hD))
  have hr : connectionOriginalClockRate (projectiveOriginalFlow y t₀ (q z)) ≠ 0 :=
    mul_ne_zero (div_ne_zero (by norm_num) (ne_of_gt (toProjectiveState_denom_pos hA hc))) hclock
  have H := (hasDerivAt_projectiveOriginalFlow_time hD ht hA).scomp z hq
  rw [projectiveOriginalField_connectionLog hclock] at H
  simpa only [Function.comp_def, smul_smul, one_div_mul_cancel hr, one_smul] using H

/-- No independent variational equation is assumed: the tangent comes from the exact Einstein flow. -/
theorem hasDerivAt_connectionLogFlowVariation {y : ProjectiveState} {t₀ z : ℝ} {q : ℝ → ℝ}
    (hD : 0 < projectiveStateDenom y) (ht : q z ∈ normalizedMaxDomain (fromProjectiveState y) t₀)
    (hA : 0 < 1 + normalizedMaxCurve (fromProjectiveState y) t₀ (q z) 0)
    (hm : 1 < -projectiveOriginalFlow y t₀ (q z) 0)
    (hclock : connectionClockRate (projectiveOriginalFlow y t₀ (q z)) ≠ 0)
    (hf : matchingPhaseSlope (-projectiveOriginalFlow y t₀ (q z) 0)
      (projectiveOriginalFlow y t₀ (q z) 2) (projectiveOriginalFlow y t₀ (q z) 3) ≠ 0)
    (hu : projectiveOriginalFlow y t₀ (q z) 1 ≠ 0) (hv : projectiveOriginalFlow y t₀ (q z) 2 ≠ 0)
    (hw : projectiveOriginalFlow y t₀ (q z) 3 ≠ 0)
    (hq : HasDerivAt q (1 / connectionOriginalClockRate (projectiveOriginalFlow y t₀ (q z))) z)
    (v : ProjectiveState) :
    HasDerivAt (fun r => connectionLogFlowVariation y t₀ (q r) v)
      (connectionLogLinearizedRates (projectiveOriginalFlow y t₀ (q z))
        (connectionLogFlowVariation y t₀ (q z) v)) z :=
  hasDerivAt_connectionLogTangent (hasDerivAt_projectiveOriginalFlow_connectionLog hD ht hA hclock hq)
    (hasDerivAt_connectionProjectedFlowVariation_log hD ht hA hw hclock hq v) hm hclock hf hu hv hw

theorem connectionLogFlowVariation_initial {y : ProjectiveState}
    (hD : 0 < projectiveStateDenom y) (t₀ : ℝ) (v : ProjectiveState) :
    connectionLogFlowVariation y t₀ t₀ v = connectionLogTangent y v := by
  rw [connectionLogFlowVariation, projectiveOriginalFlow_initial hD, connectionProjectedFlowVariation_initial hD]

theorem connectionLogFlowVariation_wall {y : ProjectiveState} {t₀ t : ℝ} (v : ProjectiveState)
    (hD : connectionClockRate (projectiveOriginalFlow y t₀ t) ≠ 0)
    (hw : projectiveOriginalFlow y t₀ t 3 ≠ 0) :
    connectionLogFlowVariation y t₀ t v 3 = v 3 / y 3 := by
  change connectionClockProjection _ _ _ 3 / projectiveOriginalFlow y t₀ t 3 = _
  rw [connectionClockProjection_wall hD hw, mul_div_cancel_right₀ _ hw]

theorem connectionLogTangent_entry (μ u w : ℝ) (d : Fin 3 → ℝ) :
    connectionLogTangent (connectionEntry μ u w) ![-d 0, d 1, 0, d 2] =
      ![matchingPhaseSlope μ 1 w * d 0 + w / phaseNorm (μ - 1) w * d 2, d 1 / u, 0, d 2 / w] := by
  ext i
  fin_cases i <;> simp [connectionLogTangent, connectionEntry]

end BianchiIX
