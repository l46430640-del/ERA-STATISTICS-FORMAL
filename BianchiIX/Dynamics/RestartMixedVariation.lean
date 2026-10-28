import BianchiIX.Dynamics.RestartMixedFlow

noncomputable section

namespace BianchiIX

open Set

/-- The integrated coefficient controls the actual initial-state derivative, without a dimension factor. -/
theorem restartMixedFlow_fderiv_bound {C h b T : ℝ} {y : RestartState}
    (H : ∀ t ∈ Icc (0 : ℝ) T, restartMixedFlowRegular (y, t))
    (HA : ∀ t ∈ Icc (0 : ℝ) T,
      ‖fderiv ℝ restartMixedField (restartMixedFlow (y, t))‖ ≤ C * (h * Real.exp (-2 * t) + b)) :
    ∀ t ∈ Icc (0 : ℝ) T,
      ‖fderiv ℝ (fun z => restartMixedFlow (z, t)) y‖ ≤ Real.exp (restartFastBudget C h b t) := by
  intro t ht
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.exp_pos _).le
  intro v
  have HD (s : ℝ) (hs : s ∈ Icc (0 : ℝ) T) := hasDerivAt_restartMixedFlow_variation (H s hs) v
  have HB (s : ℝ) (hs : s ∈ Icc (0 : ℝ) T) :
      ‖fderiv ℝ restartMixedField (restartMixedFlow (y, s)) (fderiv ℝ restartMixedFlow (y, s) (v, 0))‖ ≤
        (C * (h * Real.exp (-2 * s) + b)) * ‖fderiv ℝ restartMixedFlow (y, s) (v, 0)‖ :=
    ((fderiv ℝ restartMixedField (restartMixedFlow (y, s))).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (HA s hs) (norm_nonneg _))
  have HG := norm_le_exp_of_norm_deriv_clock HD (fun s _ => hasDerivAt_restartFastBudget C h b s) HB t ht
  rw [restartMixedFlow_variation_initial (H t ht).1, restartFastBudget_zero, sub_zero] at HG
  rw [fderiv_parameterSlice_apply ((contDiffAt_restartMixedFlow_two (H t ht)).differentiableAt (by norm_num)) v]
  simpa only [mul_comm] using HG

/-- The nonlinear continuation supplies both joint regularity and the pointwise budget along the actual flow. -/
theorem restartMixedFlow_fastLayer_regular {C h b T : ℝ} {y : RestartState}
    (hC : 0 ≤ C)
    (hF : ∀ w : RestartState, ‖w‖ ≤ 1 / 16 → ‖fderiv ℝ restartCompactField w‖ ≤ C * ‖w‖)
    (hh : 0 < h ∧ h ≤ 1 / 128) (hb : 0 < b ∧ b ≤ 1 / 16) (hT : 0 ≤ T)
    (hbudget : C * h / 2 + C * b * T ≤ 1 / 4)
    (hn : Real.exp (y 0) ≤ h) (hZ : ‖restartCompactCenterProjection y‖ ≤ b / 2) :
    ∀ t ∈ Icc (0 : ℝ) T, restartMixedFlowRegular (y, t) ∧
      ‖restartExpCoordinates (restartMixedFlow (y, t))‖ ≤ 1 / 16 ∧
      ‖restartExpCoordinates (restartMixedFlow (y, t))‖ ≤ h * Real.exp (-2 * t) + b := by
  have hZsmall : ‖restartCompactCenterProjection y‖ ≤ 1 / 16 := by linarith only [hZ, hb.2]
  have hybox : ‖restartExpCoordinates y‖ ≤ 1 / 16 := by
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 16)).mpr
    intro i
    fin_cases i
    · change |Real.exp (y 0)| ≤ 1 / 16
      rw [abs_of_pos (Real.exp_pos _)]
      linarith only [hn, hh.2]
    · exact (norm_le_pi_norm (restartCompactCenterProjection y) 0).trans hZsmall
    · exact (norm_le_pi_norm (restartCompactCenterProjection y) 1).trans hZsmall
    · exact (norm_le_pi_norm (restartCompactCenterProjection y) 2).trans hZsmall
  have hyrad : 0 < restartRadicand (restartExpCoordinates y) := by
    have H := (restartCompact_box_bounds hybox).2.1
    linarith only [H]
  have hc := restartMixedChart_constraint hyrad.le
  have hp : restartMixedChart y 0 < 0 := neg_lt_zero.mpr (Real.sqrt_pos.mpr hyrad)
  have hcenter : restartCenterProjection (restartMixedChart y) = restartCompactCenterProjection y := by
    ext i
    fin_cases i <;> rfl
  have H := normalized_restart_fastLayer_control hC hF hh hb hT hbudget hc hp
    ⟨Real.exp_pos _, hn⟩ (by rwa [hcenter])
  intro t ht
  have Ht := H t ht
  let x := normalizedMaxCurve (restartMixedChart y) 0 t
  have hpos : 0 < x 2 := Ht.1
  have hreg : restartMixedFlowRegular (y, t) :=
    ⟨hyrad, normalizedMaxDomain_contains_Ici_of_constraint hc 0 ht.1,
      by linarith only [Ht.2.2.1], hpos⟩
  have hnsmall : x 2 ≤ 1 / 16 := by
    have he := Real.exp_le_one_iff.mpr (by linarith only [ht.1] : -2 * t ≤ 0)
    have Hn := Ht.2.1.trans (mul_le_mul_of_nonneg_left he hh.1.le)
    linarith only [Hn, hh.2]
  have hZt : ‖restartCenterProjection x‖ ≤ b := Ht.2.2.2.2.le
  have hexp : restartExpCoordinates (restartMixedFlow (y, t)) = restartPhysicalCoordinates x :=
    restartExpCoordinates_mixed hpos
  refine ⟨hreg, ?_, ?_⟩
  · rw [hexp]
    exact restartPhysicalCoordinates_norm_le (by norm_num)
      (by rwa [abs_of_pos hpos]) (hZt.trans hb.2)
  · rw [hexp]
    have hB : 0 ≤ h * Real.exp (-2 * t) + b :=
      add_nonneg (mul_nonneg hh.1.le (Real.exp_pos _).le) hb.1.le
    apply restartPhysicalCoordinates_norm_le hB
    · rw [abs_of_pos hpos]
      exact Ht.2.1.trans (le_add_of_nonneg_right hb.1.le)
    · exact hZt.trans (le_add_of_nonneg_left (mul_nonneg hh.1.le (Real.exp_pos _).le))

theorem restartMixedFlow_fastLayer_derivative {C h b T : ℝ} {y : RestartState}
    (hC : 0 ≤ C)
    (hF : ∀ w : RestartState, ‖w‖ ≤ 1 / 16 → ‖fderiv ℝ restartCompactField w‖ ≤ C * ‖w‖)
    (hM : ∀ z : RestartState, ‖restartExpCoordinates z‖ ≤ 1 / 16 →
      ‖fderiv ℝ restartMixedField z‖ ≤ C * ‖restartExpCoordinates z‖)
    (hh : 0 < h ∧ h ≤ 1 / 128) (hb : 0 < b ∧ b ≤ 1 / 16) (hT : 0 ≤ T)
    (hbudget : C * h / 2 + C * b * T ≤ 1 / 4)
    (hn : Real.exp (y 0) ≤ h) (hZ : ‖restartCompactCenterProjection y‖ ≤ b / 2) :
    ∀ t ∈ Icc (0 : ℝ) T,
      ContDiffAt ℝ 2 restartMixedFlow (y, t) ∧
      ‖fderiv ℝ (fun z => restartMixedFlow (z, t)) y‖ ≤ Real.exp (1 / 4) ∧
      ‖fderiv ℝ (fun z => restartMixedFlow (z, t)) y‖ < 2 := by
  have H := restartMixedFlow_fastLayer_regular hC hF hh hb hT hbudget hn hZ
  have HA (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      ‖fderiv ℝ restartMixedField (restartMixedFlow (y, t))‖ ≤ C * (h * Real.exp (-2 * t) + b) :=
    (hM _ (H t ht).2.1).trans (mul_le_mul_of_nonneg_left (H t ht).2.2 hC)
  have HD := restartMixedFlow_fderiv_bound (fun t ht => (H t ht).1) HA
  intro t ht
  have HE := (restartFastBudget_le hC hh.1.le hb.1.le ht.2).trans hbudget
  have HB := (HD t ht).trans (Real.exp_le_exp.mpr HE)
  exact ⟨contDiffAt_restartMixedFlow_two (H t ht).1, HB, HB.trans_lt exp_one_quarter_lt_two⟩

/-- The bound on the true four-coordinate flow is uniform in height, cutoff, and zero weak walls. -/
theorem exists_restartMixedFlow_fastLayer_derivative :
    ∃ C ≥ (32 : ℝ), ∀ (h b T : ℝ) (y : RestartState),
      0 < h → C * h ≤ 1 / 4 → (0 < b ∧ b ≤ 1 / 16) → 0 ≤ T →
      C * b * T ≤ 1 / 8 → Real.exp (y 0) ≤ h → ‖restartCompactCenterProjection y‖ ≤ b / 2 →
      ∀ t ∈ Icc (0 : ℝ) T,
        ContDiffAt ℝ 2 restartMixedFlow (y, t) ∧
        ‖fderiv ℝ (fun z => restartMixedFlow (z, t)) y‖ ≤ Real.exp (1 / 4) ∧
        ‖fderiv ℝ (fun z => restartMixedFlow (z, t)) y‖ < 2 := by
  obtain ⟨A, _, HA⟩ := exists_restartCompact_derivative_bounds
  obtain ⟨B, _, HB⟩ := exists_restartMixed_derivative_bounds
  let C := max 32 (max A B)
  have hC : 32 ≤ C := le_max_left _ _
  have hC0 : 0 ≤ C := le_trans (by norm_num : (0 : ℝ) ≤ 32) hC
  have hA : A ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hB : B ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  have hF (w : RestartState) (hw : ‖w‖ ≤ 1 / 16) : ‖fderiv ℝ restartCompactField w‖ ≤ C * ‖w‖ :=
    (HA w hw).1.trans (mul_le_mul_of_nonneg_right hA (norm_nonneg _))
  have hM (z : RestartState) (hz : ‖restartExpCoordinates z‖ ≤ 1 / 16) :
      ‖fderiv ℝ restartMixedField z‖ ≤ C * ‖restartExpCoordinates z‖ :=
    (HB z hz).1.trans (mul_le_mul_of_nonneg_right hB (norm_nonneg _))
  refine ⟨C, hC, ?_⟩
  intro h b T y hh hCh hb hT hCb hn hZ
  have hhsmall : h ≤ 1 / 128 := by
    nlinarith only [hCh, mul_le_mul_of_nonneg_right hC hh.le]
  exact restartMixedFlow_fastLayer_derivative hC0 hF hM ⟨hh, hhsmall⟩ hb hT
    (by linarith only [hCh, hCb]) hn hZ

end BianchiIX
