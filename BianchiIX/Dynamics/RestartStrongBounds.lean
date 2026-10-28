import BianchiIX.Dynamics.RestartStrongCoordinates
import BianchiIX.Analysis.LogRatioBound

noncomputable section

namespace BianchiIX

open Set

/-- Relative strong-wall control and ordinary initial derivatives, uniform down to the zero weak walls. -/
theorem exists_restartSectionStrong_bounds :
    ∃ C ≥ (32 : ℝ), ∀ (h b T : ℝ),
      0 < h → C * h ≤ 1 / 4 → (0 < b ∧ b ≤ 1 / 16) → 0 ≤ T → C * b * T ≤ 1 / 8 →
      ∀ t ∈ Icc (0 : ℝ) T, ∀ Z : RestartCenterState, ‖Z‖ ≤ b / 2 →
        0 < restartSectionStrongWall h t Z ∧ 0 < restartReferenceCurve h t 2 ∧
        |Real.log (restartSectionStrongWall h t Z / restartReferenceCurve h t 2)| ≤ 2 * ‖Z‖ ∧
        |restartSectionStrongWall h t Z - restartReferenceCurve h t 2| ≤ 4 * ‖Z‖ * restartReferenceCurve h t 2 ∧
        DifferentiableAt ℝ (restartSectionStrongLog h t) Z ∧
        DifferentiableAt ℝ (restartSectionStrongWall h t) Z ∧
        ‖fderiv ℝ (restartSectionStrongLog h t) Z‖ ≤ 2 ∧
        ‖fderiv ℝ (restartSectionStrongWall h t) Z‖ ≤ 2 * restartSectionStrongWall h t Z := by
  obtain ⟨C, hC, HC⟩ := exists_restartSectionMixedFlow_derivative
  refine ⟨C, hC, ?_⟩
  intro h b T hh hCh hb hT hCb t ht Z hZ
  have hhsmall : |h| ≤ 1 / 16 := by
    rw [abs_of_pos hh]
    nlinarith only [hC, hCh, hh]
  have hZsmall : ‖Z‖ ≤ 1 / 16 := by linarith only [hZ, hb.2]
  have hrad := restartSectionRadicand_pos_of_small hhsmall hZsmall
  have hrad0 := restartSectionRadicand_pos_of_small hhsmall (by simp : ‖(0 : RestartCenterState)‖ ≤ 1 / 16)
  have hn := restartSectionStrongWall_pos hh hrad.le ht.1
  have hn0 := restartSectionStrongWall_pos hh hrad0.le ht.1
  rw [restartSectionStrongWall_zero] at hn0
  have HD := (HC h b T hh hCh hb hT hCb t ht).1 Z hZ
  have Hdiff := (HC h b T hh hCh hb hT hCb t ht).2 Z 0 hZ
    (by simpa only [norm_zero] using div_nonneg hb.1.le (by norm_num : (0 : ℝ) ≤ 2))
  have Hcoord := norm_le_pi_norm (restartSectionMixedFlow h t Z - restartSectionMixedFlow h t 0) 0
  have Hlog : |Real.log (restartSectionStrongWall h t Z / restartReferenceCurve h t 2)| ≤ 2 * ‖Z‖ := by
    rw [Real.log_div hn.ne' hn0.ne', ← restartSectionStrongWall_zero h t]
    change |restartSectionStrongLog h t Z - restartSectionStrongLog h t 0| ≤ 2 * ‖Z‖
    rw [restartSectionStrongLog_eq hh, restartSectionStrongLog_eq hh]
    exact Hcoord.trans (Hdiff.trans (by
      simpa only [sub_zero] using mul_le_mul_of_nonneg_right exp_one_quarter_lt_two.le (norm_nonneg Z)))
  have Hrel := abs_sub_le_of_log_ratio hn hn0 Hlog (by linarith only [hZsmall])
  have HlogD := hasFDerivAt_restartSectionStrongLog hh HD.1
  have HwallD := hasFDerivAt_restartSectionStrongWall hh hrad ht.1 HD.1
  have Hbound := (restartSectionStrongLog_fderiv_norm_le hh HD.1).trans (HD.2.trans exp_one_quarter_lt_two.le)
  refine ⟨hn, hn0, Hlog, ?_, HlogD.differentiableAt, HwallD.differentiableAt, Hbound, ?_⟩
  · nlinarith only [Hrel]
  · rw [restartSectionStrongWall_fderiv_norm hh hrad ht.1 HD.1]
    nlinarith only [Hbound, hn]

end BianchiIX
