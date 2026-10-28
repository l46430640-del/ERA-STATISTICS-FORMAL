import BianchiIX.Dynamics.RestartWeakMultipliers

noncomputable section

namespace BianchiIX

open Set Filter MeasureTheory

theorem restartWeakLogMultiplier_budget {y : RestartState} {T C h b : ℝ}
    (hT : 0 ≤ T) (hC : 0 ≤ C) (hh : 0 ≤ h) (hb : 0 ≤ b)
    (HG : ∀ t ∈ Icc (0 : ℝ) T,
      ‖restartMixedWeakRates (restartMixedFlow (y, t))‖ ≤ C * (h * Real.exp (-2 * t) + b)) (i : Fin 2) :
    |restartWeakLogMultiplier T i y| ≤ C * h / 2 + C * b * T := by
  have hc : Continuous (fun t : ℝ => C * (h * Real.exp (-2 * t) + b)) := by fun_prop
  have HI := intervalIntegral.norm_integral_le_of_norm_le (μ := volume)
    (f := fun t => restartWeakRateIntegrand i (y, t)) hT
    (Eventually.of_forall fun t (ht : t ∈ Ioc (0 : ℝ) T) =>
      (norm_le_pi_norm (restartMixedWeakRates (restartMixedFlow (y, t))) i).trans (HG t ⟨ht.1.le, ht.2⟩))
    (hc.intervalIntegrable 0 T)
  have HE := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t (_ : t ∈ uIcc (0 : ℝ) T) => hasDerivAt_restartFastBudget C h b t) (hc.intervalIntegrable 0 T)
  rw [HE, restartFastBudget_zero, sub_zero] at HI
  exact HI.trans (restartFastBudget_le hC hh hb le_rfl)

theorem restartWeakMultiplier_bounds_of_log {y : RestartState} {T : ℝ} {i : Fin 2}
    (H : |restartWeakLogMultiplier T i y| ≤ 1 / 4) :
    (1 / 2 < restartWeakMultiplier T i y ∧ restartWeakMultiplier T i y < 2) ∧
      (restartWeakMultiplier T i y)⁻¹ < 2 := by
  have hu := (Real.exp_le_exp.mpr (le_abs_self _ |>.trans H)).trans_lt exp_one_quarter_lt_two
  have hl := (Real.exp_le_exp.mpr ((neg_le_abs _).trans H)).trans_lt exp_one_quarter_lt_two
  change restartWeakMultiplier T i y < 2 at hu
  rw [Real.exp_neg] at hl
  change (restartWeakMultiplier T i y)⁻¹ < 2 at hl
  have hp := restartWeakMultiplier_pos T i y
  have Hmul := mul_lt_mul_of_pos_left hl hp
  rw [mul_inv_cancel₀ hp.ne'] at Hmul
  exact ⟨⟨by linarith only [Hmul], hu⟩, hl⟩

/-- All regularity and budget hypotheses are supplied by the actual nonlinear Einstein flow. -/
theorem exists_restartWeakMultiplier_bounds :
    ∃ C ≥ (32 : ℝ), ∀ (h b T : ℝ) (y : RestartState),
      0 < h → C * h ≤ 1 / 4 → (0 < b ∧ b ≤ 1 / 16) → 0 ≤ T → C * b * T ≤ 1 / 8 →
      Real.exp (y 0) ≤ h → ‖restartCompactCenterProjection y‖ ≤ b / 2 →
      ∀ i : Fin 2,
        restartMixedFlow (y, T) (i.addNat 2) = y (i.addNat 2) * restartWeakMultiplier T i y ∧
        |restartWeakLogMultiplier T i y| ≤ 1 / 4 ∧
        (1 / 2 < restartWeakMultiplier T i y ∧ restartWeakMultiplier T i y < 2) ∧
        (restartWeakMultiplier T i y)⁻¹ < 2 ∧
        ContDiffAt ℝ 2 (restartWeakLogMultiplier T i) y ∧
        ContDiffAt ℝ 2 (restartWeakMultiplier T i) y ∧
        ‖fderiv ℝ (restartWeakLogMultiplier T i) y‖ ≤ 2 * C * T ∧
        ‖fderiv ℝ (restartWeakMultiplier T i) y‖ ≤ 4 * C * T := by
  obtain ⟨A, _, HA⟩ := exists_restartCompact_derivative_bounds
  obtain ⟨B, hB, HB⟩ := exists_restartMixed_fastLayer_bounds
  let C := max A B
  have hAC : A ≤ C := le_max_left _ _
  have hBC : B ≤ C := le_max_right _ _
  have hC : 32 ≤ C := hB.trans hBC
  have hC0 : 0 ≤ C := le_trans (by norm_num : (0 : ℝ) ≤ 32) hC
  have hF (w : RestartState) (hw : ‖w‖ ≤ 1 / 16) : ‖fderiv ℝ restartCompactField w‖ ≤ C * ‖w‖ :=
    (HA w hw).1.trans (mul_le_mul_of_nonneg_right hAC (norm_nonneg _))
  have hM (w : RestartState) (hw : ‖restartExpCoordinates w‖ ≤ 1 / 16) :
      ‖fderiv ℝ restartMixedField w‖ ≤ C * ‖restartExpCoordinates w‖ :=
    (HB w hw).1.trans (mul_le_mul_of_nonneg_right hBC (norm_nonneg _))
  refine ⟨C, hC, ?_⟩
  intro h b T y hh hCh hb hT hCb hn hZ i
  have hhsmall : h ≤ 1 / 128 := by
    nlinarith only [hCh, mul_le_mul_of_nonneg_right hC hh.le]
  have hbudget : C * h / 2 + C * b * T ≤ 1 / 4 := by linarith only [hCh, hCb]
  have HR := restartMixedFlow_fastLayer_regular hC0 hF ⟨hh, hhsmall⟩ hb hT hbudget hn hZ
  have HD := restartMixedFlow_fastLayer_derivative hC0 hF hM ⟨hh, hhsmall⟩ hb hT hbudget hn hZ
  have HG (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      ‖restartMixedWeakRates (restartMixedFlow (y, t))‖ ≤ C * (h * Real.exp (-2 * t) + b) :=
    ((HB _ (HR t ht).2.1).2.2.1.trans
      (mul_le_mul_of_nonneg_right hBC (norm_nonneg _))).trans
      (mul_le_mul_of_nonneg_left (HR t ht).2.2 hC0)
  have Hlog := (restartWeakLogMultiplier_budget hT hC0 hh.le hb.1.le HG i).trans hbudget
  have Hbounds := restartWeakMultiplier_bounds_of_log Hlog
  have Hreg := contDiffAt_restartWeakLogMultiplier_two hT (fun t ht => (HR t ht).1) i
  have Hder := restartWeakLogMultiplier_derivative_bound hT hC0 (fun t ht => (HR t ht).1)
    (fun t ht => (HB _ (HR t ht).2.1).2.2.2.1.trans hBC)
    (fun t ht => (HD t ht).2.2.le) i
  refine ⟨restartWeakMultiplier_formula hT (fun t ht => (HR t ht).1) i,
    Hlog, Hbounds.1, Hbounds.2, Hreg, Hreg.exp, Hder, ?_⟩
  have HE := ((Hreg.differentiableAt (by norm_num)).hasFDerivAt.exp).fderiv
  change fderiv ℝ (restartWeakMultiplier T i) y =
    restartWeakMultiplier T i y • fderiv ℝ (restartWeakLogMultiplier T i) y at HE
  rw [HE, norm_smul, Real.norm_eq_abs, abs_of_pos (restartWeakMultiplier_pos T i y)]
  calc
    _ ≤ 2 * ‖fderiv ℝ (restartWeakLogMultiplier T i) y‖ :=
      mul_le_mul_of_nonneg_right Hbounds.1.2.le (norm_nonneg _)
    _ ≤ 4 * C * T := by linarith only [Hder]

end BianchiIX
