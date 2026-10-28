import BianchiIX.Dynamics.ConnectionPhaseFeedback

noncomputable section

namespace BianchiIX

open Set

/-- Uniform phase and transverse bounds for the actual radial initial derivative. -/
theorem connectionLog_actual_radial_variation_bounds {y : ProjectiveState} {q : ℝ → ℝ}
    {t₀ μ a b : ℝ} (hab : a ≤ b) (hμ : 4 ≤ μ) (hden : 0 < projectiveStateDenom y)
    (hdom : ∀ z ∈ Icc a b, q z ∈ normalizedMaxDomain (fromProjectiveState y) t₀)
    (hchart : ∀ z ∈ Icc a b, 0 < 1 + normalizedMaxCurve (fromProjectiveState y) t₀ (q z) 0)
    (hm : ∀ z ∈ Icc a b, |-projectiveOriginalFlow y t₀ (q z) 0 - μ| ≤ 1 / 2)
    (hu : ∀ z ∈ Icc a b, 0 < projectiveOriginalFlow y t₀ (q z) 1 ∧
      projectiveOriginalFlow y t₀ (q z) 1 ≤ 1 / 10000)
    (hv : ∀ z ∈ Icc a b, 0 < projectiveOriginalFlow y t₀ (q z) 2 ∧
      projectiveOriginalFlow y t₀ (q z) 2 ≤ 1)
    (hw : ∀ z ∈ Icc a b, 0 < projectiveOriginalFlow y t₀ (q z) 3 ∧
      projectiveOriginalFlow y t₀ (q z) 3 ≤ 1)
    (hentry : y 1 ≤ y 2) (hsmall : y 1 ≤ (1 / 10000) / μ) (hwall : y 3 ≤ 1 / 10000)
    (hq : ∀ z ∈ Icc a b,
      HasDerivAt q (1 / connectionOriginalClockRate (projectiveOriginalFlow y t₀ (q z))) z)
    (hqa : q a = t₀) (v : ProjectiveState) (hv1 : v 1 = 0) (hv2 : v 2 = 0) (hv3 : v 3 = 0) :
    ∀ t ∈ Icc a b, |connectionLogFlowVariation y t₀ (q t) v 0| ≤ (16 / 15) * |v 0| ∧
      |connectionLogFlowVariation y t₀ (q t) v 0 - connectionLogTangent y v 0| ≤
        (16 / 15) * connectionPhaseFeedbackBudget μ (y 1) (y 2 * y 3) * |v 0| ∧
      ‖connectionWeightedTangent μ (connectionLogFlowVariation y t₀ (q t) v)‖ ≤
        (2048 / 15) * (t - a) * |v 0| := by
  have hu' (z : ℝ) (hz : z ∈ Icc a b) : 0 ≤ projectiveOriginalFlow y t₀ (q z) 1 ∧
      projectiveOriginalFlow y t₀ (q z) 1 ≤ 1 / 10000 := ⟨(hu z hz).1.le, (hu z hz).2⟩
  have hv' (z : ℝ) (hz : z ∈ Icc a b) : 0 ≤ projectiveOriginalFlow y t₀ (q z) 2 ∧
      projectiveOriginalFlow y t₀ (q z) 2 ≤ 1 := ⟨(hv z hz).1.le, (hv z hz).2⟩
  have hw' (z : ℝ) (hz : z ∈ Icc a b) : 0 ≤ projectiveOriginalFlow y t₀ (q z) 3 ∧
      projectiveOriginalFlow y t₀ (q z) 3 ≤ 1 := ⟨(hw z hz).1.le, (hw z hz).2⟩
  have hclock (z : ℝ) (hz : z ∈ Icc a b) : connectionClockRate (projectiveOriginalFlow y t₀ (q z)) ≠ 0 := by
    have H := (connection_speed_bounds hμ (hm z hz) (hu' z hz) (hv' z hz) (hw' z hz)).1
    change μ / 2 ≤ connectionClockRate (projectiveOriginalFlow y t₀ (q z)) at H
    linarith only [H, hμ]
  have hfield (z : ℝ) (hz : z ∈ Icc a b) :=
    hasDerivAt_projectiveOriginalFlow_connectionLog (y := y) (t₀ := t₀) (z := z) (q := q)
      hden (hdom z hz) (hchart z hz) (hclock z hz) (hq z hz)
  have hvar (z : ℝ) (hz : z ∈ Icc a b) :=
    hasDerivAt_connectionLogFlowVariation (y := y) (t₀ := t₀) (z := z) (q := q)
      hden (hdom z hz) (hchart z hz)
      (by linarith only [hμ, (abs_le.mp (hm z hz)).1]) (hclock z hz)
      (by have H := (matchingPhase_slope_bounds hμ (hm z hz) (hv' z hz) (hw' z hz)).1; linarith only [H])
      (ne_of_gt (hu z hz).1) (ne_of_gt (hv z hz).1) (ne_of_gt (hw z hz).1) (hq z hz) v
  have hinit : projectiveOriginalFlow y t₀ (q a) = y := by rw [hqa, projectiveOriginalFlow_initial hden]
  have hdinit : connectionLogFlowVariation y t₀ (q a) v = connectionLogTangent y v := by
    rw [hqa, connectionLogFlowVariation_initial hden]
  have H := connectionLog_radial_variation_bounds
    (Y := fun z => projectiveOriginalFlow y t₀ (q z)) (D := fun z => connectionLogFlowVariation y t₀ (q z) v)
    hab hμ hfield hm hu' hv hw'
    (by simpa only [hinit] using hentry) (by simpa only [hinit] using hsmall) (by simpa only [hinit] using hwall) hvar
    (fun z hz => by rw [connectionLogFlowVariation_wall v (hclock z hz) (ne_of_gt (hw z hz).1), hv3, zero_div])
    (by simp [hdinit, connectionLogTangent, hv1]) (by simp [hdinit, connectionLogTangent, hv2])
  have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hF : 3 / 4 ≤ matchingPhaseSlope (-y 0) (y 2) (y 3) ∧
      matchingPhaseSlope (-y 0) (y 2) (y 3) ≤ 1 := by
    simpa only [hinit] using matchingPhase_slope_bounds hμ (hm a ha) (hv' a ha) (hw' a ha)
  have hF0 : 0 ≤ matchingPhaseSlope (-y 0) (y 2) (y 3) := by linarith only [hF.1]
  have hZ : |connectionLogTangent y v 0| ≤ |v 0| := by
    simp only [connectionLogTangent, Matrix.cons_val_zero, hv2, hv3, mul_zero, add_zero,
      abs_mul, abs_neg, abs_of_nonneg hF0]
    exact (mul_le_mul_of_nonneg_right hF.2 (abs_nonneg _)).trans_eq (one_mul _)
  have hu0 : 0 ≤ y 1 := by simpa only [hinit] using (hu' a ha).1
  have hB0 : 0 ≤ connectionPhaseFeedbackBudget μ (y 1) (y 2 * y 3) :=
    connectionPhaseFeedbackBudget_nonneg (by linarith only [hμ]) hu0
  intro t ht
  have Ht := H t ht
  rw [hinit, hdinit] at Ht
  refine ⟨Ht.1.trans (mul_le_mul_of_nonneg_left hZ (by norm_num)),
    Ht.2.1.trans (mul_le_mul_of_nonneg_left hZ (by positivity)), ?_⟩
  have hta : 0 ≤ t - a := sub_nonneg.mpr ht.1
  exact Ht.2.2.trans (mul_le_mul_of_nonneg_left hZ (by positivity))

end BianchiIX
