import BianchiIX.Dynamics.RestartRadialObservable
import BianchiIX.Analysis.ScalarClockComparison

noncomputable section

namespace BianchiIX

open Set

/-- One common budget controls the actual orbit and prevents degeneration of its radial quadratic form. -/
theorem exists_restartSectionQuadratic_control :
    ∃ C ≥ (32 : ℝ), ∀ (h b T : ℝ) (Z : RestartCenterState),
      0 < h → C * h ≤ 1 / 4 → (0 < b ∧ b ≤ 1 / 16) → 0 ≤ T → C * b * T ≤ 1 / 8 → ‖Z‖ ≤ b / 2 →
      ∀ t ∈ Icc (0 : ℝ) T,
        0 < restartSectionStrongWall h t Z ∧ restartSectionStrongWall h t Z ≤ h * Real.exp (-2 * t) ∧
        restartSectionStrongWall h t Z ≤ 1 / 16 ∧ ‖restartSectionCenterFlow h t Z‖ ≤ b ∧
        HasDerivAt (fun s => restartSectionQuadratic h s Z) (restartSectionQuadraticRate h t Z) t ∧
        |restartSectionQuadraticRate h t Z| ≤ C *
          (restartSectionStrongWall h t Z * ‖restartSectionCenterFlow h t Z‖ + ‖restartSectionCenterFlow h t Z‖ ^ 2) *
            restartSectionQuadratic h t Z ∧
        restartSectionQuadratic h 0 Z / 2 ≤ restartSectionQuadratic h t Z ∧
        restartSectionQuadratic h t Z ≤ 2 * restartSectionQuadratic h 0 Z := by
  obtain ⟨A, hA, HA⟩ := exists_restartSection_fastLayer_control
  obtain ⟨B, _, HB⟩ := exists_restartRadialDrift_bounds
  let C := max A B
  have hAC : A ≤ C := le_max_left _ _
  have hBC : B ≤ C := le_max_right _ _
  have hC : 32 ≤ C := hA.trans hAC
  have hC0 : 0 ≤ C := le_trans (by norm_num : (0 : ℝ) ≤ 32) hC
  refine ⟨C, hC, ?_⟩
  intro h b T Z hh hCh hb hT hCb hZ
  have HAh : A * h ≤ 1 / 4 := (mul_le_mul_of_nonneg_right hAC hh.le).trans hCh
  have HAb : A * b * T ≤ 1 / 8 :=
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hAC hb.1.le) hT).trans hCb
  have HF := HA h b T Z hh HAh hb hT HAb hZ
  have hhsmall : h ≤ 1 / 128 := by nlinarith only [hC, hCh, hh]
  have hrad := restartSectionRadicand_pos_of_small (h := h) (Z := Z)
    (by rw [abs_of_pos hh]; linarith only [hhsmall]) (by linarith only [hZ, hb.2])
  have Hn (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      0 < restartSectionStrongWall h t Z ∧ restartSectionStrongWall h t Z ≤ 1 / 16 := by
    have HE := Real.exp_le_one_iff.mpr (by linarith only [ht.1] : -2 * t ≤ 0)
    exact ⟨(HF t ht).1, (HF t ht).2.1.trans
      ((mul_le_mul_of_nonneg_left HE hh.le).trans (by linarith only [hhsmall]))⟩
  have Hz (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : ‖restartSectionCenterFlow h t Z‖ ≤ b :=
    (HF t ht).2.2.2.2.le
  have HD (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      HasDerivAt (fun s => restartSectionQuadratic h s Z) (restartSectionQuadraticRate h t Z) t :=
    hasDerivAt_restartSectionQuadratic hrad.le ht.1
      (by linarith only [(HF t ht).2.2.1])
      (by nlinarith only [(Hn t ht).1, (Hn t ht).2])
  have HR (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      |restartSectionQuadraticRate h t Z| ≤ C *
        (restartSectionStrongWall h t Z * ‖restartSectionCenterFlow h t Z‖ + ‖restartSectionCenterFlow h t Z‖ ^ 2) *
          restartSectionQuadratic h t Z := by
    have H := (HB _ _ ⟨(Hn t ht).1.le, (Hn t ht).2⟩ ((Hz t ht).trans hb.2)).2.1
    exact H.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hBC (add_nonneg
        (mul_nonneg (Hn t ht).1.le (norm_nonneg _)) (sq_nonneg _)))
      (restartSectionQuadratic_nonneg h t Z))
  have HG (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      |restartSectionQuadraticRate h t Z| ≤ C * (h * Real.exp (-2 * t) + b) * restartSectionQuadratic h t Z := by
    have hr1 : ‖restartSectionCenterFlow h t Z‖ ≤ 1 := (Hz t ht).trans (by linarith only [hb.2])
    have Hcoeff : restartSectionStrongWall h t Z * ‖restartSectionCenterFlow h t Z‖ +
        ‖restartSectionCenterFlow h t Z‖ ^ 2 ≤ h * Real.exp (-2 * t) + b := by
      have Hs : ‖restartSectionCenterFlow h t Z‖ ^ 2 ≤ ‖restartSectionCenterFlow h t Z‖ := by
        nlinarith only [mul_nonneg (norm_nonneg (restartSectionCenterFlow h t Z)) (sub_nonneg.mpr hr1)]
      have Hn' := mul_le_mul_of_nonneg_left hr1 (Hn t ht).1.le
      have HE : restartSectionStrongWall h t Z ≤ h * Real.exp (-2 * t) := (HF t ht).2.1
      nlinarith only [Hs, Hn', HE, Hz t ht]
    exact (HR t ht).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left Hcoeff hC0) (restartSectionQuadratic_nonneg h t Z))
  have Hcomp := scalar_clock_comparison HD (fun t _ => hasDerivAt_restartFastBudget C h b t) HG
  intro t ht
  have HE : restartFastBudget C h b t ≤ 1 / 4 :=
    (restartFastBudget_le hC0 hh.le hb.1.le ht.2).trans (by linarith only [hCh, hCb])
  have Hexp := (Real.exp_le_exp.mpr HE).trans exp_one_quarter_lt_two.le
  have Hinv : 1 / 2 ≤ Real.exp (-restartFastBudget C h b t) := by
    have H := mul_le_mul_of_nonneg_right Hexp (Real.exp_pos (-restartFastBudget C h b t)).le
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at H
    linarith only [H]
  have HC := Hcomp t ht
  rw [restartFastBudget_zero, sub_zero] at HC
  refine ⟨(Hn t ht).1, (HF t ht).2.1, (Hn t ht).2, Hz t ht, HD t ht, HR t ht, ?_, ?_⟩
  · have H := mul_le_mul_of_nonneg_left Hinv (restartSectionQuadratic_nonneg h 0 Z)
    linarith only [H, HC.1]
  · exact HC.2.trans (by
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left Hexp (restartSectionQuadratic_nonneg h 0 Z))

end BianchiIX
