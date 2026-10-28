import BianchiIX.Dynamics.RestartSectionVariation
import BianchiIX.Analysis.NormClockForcing

noncomputable section

namespace BianchiIX

open Set

/-- The forced variational equation compares the genuine derivatives at two section initial states. -/
theorem restartSectionMixedFlow_fderiv_comparison {C h b T : ℝ} {Z W : RestartCenterState}
    (hC : 0 ≤ C) (hh : 0 ≤ h) (hb : 0 ≤ b)
    (hbudget : C * h / 2 + C * b * T ≤ 1 / 4)
    (HZ : ∀ t ∈ Icc (0 : ℝ) T, restartMixedFlowRegular (restartMixedSection h Z, t))
    (HW : ∀ t ∈ Icc (0 : ℝ) T, restartMixedFlowRegular (restartMixedSection h W, t))
    (HA : ∀ t ∈ Icc (0 : ℝ) T,
      ‖fderiv ℝ restartMixedField (restartSectionMixedFlow h t Z)‖ ≤ C * (h * Real.exp (-2 * t) + b))
    (HJ : ∀ t ∈ Icc (0 : ℝ) T, ‖fderiv ℝ (restartSectionMixedFlow h t) W‖ ≤ 2)
    (HL : ∀ t ∈ Icc (0 : ℝ) T,
      ‖fderiv ℝ restartMixedField (restartSectionMixedFlow h t Z) -
        fderiv ℝ restartMixedField (restartSectionMixedFlow h t W)‖ ≤ 2 * C * ‖Z - W‖) :
    ∀ t ∈ Icc (0 : ℝ) T,
      ‖fderiv ℝ (restartSectionMixedFlow h t) Z - fderiv ℝ (restartSectionMixedFlow h t) W‖ ≤
        8 * C * t * ‖Z - W‖ := by
  intro t ht
  have ht0 : 0 ≤ t := ht.1
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  let JZ := fun s => fderiv ℝ restartMixedFlow (restartMixedSection h Z, s) (restartCenterInclusion v, 0)
  let JW := fun s => fderiv ℝ restartMixedFlow (restartMixedSection h W, s) (restartCenterInclusion v, 0)
  let A := fun s => fderiv ℝ restartMixedField (restartSectionMixedFlow h s Z)
  let B := fun s => fderiv ℝ restartMixedField (restartSectionMixedFlow h s W)
  let ε := 4 * C * ‖Z - W‖ * ‖v‖
  have hε : 0 ≤ ε := by dsimp only [ε]; positivity
  have Hder (s : ℝ) (hs : s ∈ Icc (0 : ℝ) T) :
      HasDerivAt (fun r => JZ r - JW r) (A s (JZ s) - B s (JW s)) s :=
    (hasDerivAt_restartMixedFlow_variation (HZ s hs) (restartCenterInclusion v)).sub
      (hasDerivAt_restartMixedFlow_variation (HW s hs) (restartCenterInclusion v))
  have Hbound (s : ℝ) (hs : s ∈ Icc (0 : ℝ) T) :
      ‖A s (JZ s) - B s (JW s)‖ ≤
        C * (h * Real.exp (-2 * s) + b) * ‖JZ s - JW s‖ + ε := by
    have heq : A s (JZ s) - B s (JW s) = A s (JZ s - JW s) + (A s - B s) (JW s) := by
      simp only [map_sub, sub_apply]
      abel
    have hJW : ‖JW s‖ ≤ 2 * ‖v‖ := by
      dsimp only [JW]
      rw [← restartSectionMixedFlow_fderiv_apply (HW s hs) v]
      exact ((fderiv ℝ (restartSectionMixedFlow h s) W).le_opNorm v).trans
        (mul_le_mul_of_nonneg_right (HJ s hs) (norm_nonneg v))
    rw [heq]
    apply (norm_add_le _ _).trans
    apply add_le_add
    · exact ((A s).le_opNorm _).trans (mul_le_mul_of_nonneg_right (HA s hs) (norm_nonneg _))
    · apply ((A s - B s).le_opNorm _).trans
      have Hp := mul_le_mul (HL s hs) hJW (norm_nonneg (JW s))
        (by positivity : 0 ≤ 2 * C * ‖Z - W‖)
      dsimp only [ε]
      convert! Hp using 1
      ring
  have Hclock (s : ℝ) (hs : s ∈ Icc (0 : ℝ) T) :
      restartFastBudget C h b 0 ≤ restartFastBudget C h b s := by
    rw [restartFastBudget_zero]
    have he := Real.exp_le_one_iff.mpr (by linarith only [hs.1] : -2 * s ≤ 0)
    exact mul_nonneg hC (add_nonneg (mul_nonneg (div_nonneg hh (by norm_num)) (sub_nonneg.mpr he))
      (mul_nonneg hb hs.1))
  have HG := norm_le_exp_of_norm_deriv_clock_forcing Hder
    (fun s _ => hasDerivAt_restartFastBudget C h b s) hε Hclock Hbound t ht
  have Hinit : JZ 0 - JW 0 = 0 := by
    dsimp only [JZ, JW]
    rw [restartMixedFlow_variation_initial (HZ t ht).1,
      restartMixedFlow_variation_initial (HW t ht).1, sub_self]
  rw [Hinit, norm_zero, zero_add, restartFastBudget_zero, sub_zero, sub_zero] at HG
  have HE := (Real.exp_le_exp.mpr ((restartFastBudget_le hC hh hb ht.2).trans hbudget)).trans
    exp_one_quarter_lt_two.le
  have Hfinal := HG.trans (mul_le_mul_of_nonneg_left HE (mul_nonneg hε ht.1))
  change ‖(fderiv ℝ (restartSectionMixedFlow h t) Z - fderiv ℝ (restartSectionMixedFlow h t) W) v‖ ≤ _
  rw [sub_apply, restartSectionMixedFlow_fderiv_apply (HZ t ht),
    restartSectionMixedFlow_fderiv_apply (HW t ht)]
  convert! Hfinal using 1
  dsimp only [ε]
  ring

/-- The full nonlinear first-variation comparison (E.5), for any two signed section initial states. -/
theorem exists_restartSectionMixedFlow_fderiv_comparison :
    ∃ C ≥ (32 : ℝ), ∀ (h b T : ℝ),
      0 < h → C * h ≤ 1 / 4 → (0 < b ∧ b ≤ 1 / 16) → 0 ≤ T → C * b * T ≤ 1 / 8 →
      ∀ Z W : RestartCenterState, ‖Z‖ ≤ b / 2 → ‖W‖ ≤ b / 2 →
        ∀ t ∈ Icc (0 : ℝ) T,
          ‖fderiv ℝ (restartSectionMixedFlow h t) Z - fderiv ℝ (restartSectionMixedFlow h t) W‖ ≤
            8 * C * t * ‖Z - W‖ := by
  obtain ⟨C₀, hC₀, HC₀⟩ := exists_restartSectionMixedFlow_derivative
  obtain ⟨A, _, HA⟩ := exists_restartCompact_derivative_bounds
  obtain ⟨B, _, HB, HL⟩ := exists_restartMixed_uniform_bounds
  let C := max C₀ (max A B)
  have hC₀C : C₀ ≤ C := le_max_left _ _
  have hC : 32 ≤ C := hC₀.trans hC₀C
  have hC0 : 0 ≤ C := le_trans (by norm_num : (0 : ℝ) ≤ 32) hC
  have hA : A ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hB : B ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  have hF (w : RestartState) (hw : ‖w‖ ≤ 1 / 16) : ‖fderiv ℝ restartCompactField w‖ ≤ C * ‖w‖ :=
    (HA w hw).1.trans (mul_le_mul_of_nonneg_right hA (norm_nonneg _))
  refine ⟨C, hC, ?_⟩
  intro h b T hh hCh hb hT hCb Z W hZ hW
  have hhsmall : h ≤ 1 / 128 := by
    nlinarith only [hCh, mul_le_mul_of_nonneg_right hC hh.le]
  have hbudget : C * h / 2 + C * b * T ≤ 1 / 4 := by linarith only [hCh, hCb]
  have hsmallh : C₀ * h ≤ 1 / 4 := (mul_le_mul_of_nonneg_right hC₀C hh.le).trans hCh
  have hsmallT : C₀ * b * T ≤ 1 / 8 :=
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC₀C hb.1.le) hT).trans hCb
  have HD := HC₀ h b T hh hsmallh hb hT hsmallT
  have HR (Y : RestartCenterState) (hY : ‖Y‖ ≤ b / 2) :=
    restartMixedFlow_fastLayer_regular hC0 hF ⟨hh, hhsmall⟩ hb hT hbudget
      (y := restartMixedSection h Y)
      (by change Real.exp (Real.log h) ≤ h; rw [Real.exp_log hh])
      (by rwa [restartMixedSection_center])
  have Hjac (Y : RestartCenterState) (hY : ‖Y‖ ≤ b / 2) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) T) :
      ‖fderiv ℝ restartMixedField (restartSectionMixedFlow h s Y)‖ ≤ C * (h * Real.exp (-2 * s) + b) :=
    ((HB _ (HR Y hY s hs).2.1).1.trans (mul_le_mul_of_nonneg_right hB (norm_nonneg _))).trans
      (mul_le_mul_of_nonneg_left (HR Y hY s hs).2.2 hC0)
  have Hlip (s : ℝ) (hs : s ∈ Icc (0 : ℝ) T) :
      ‖fderiv ℝ restartMixedField (restartSectionMixedFlow h s Z) -
        fderiv ℝ restartMixedField (restartSectionMixedFlow h s W)‖ ≤ 2 * C * ‖Z - W‖ := by
    have H1 := (HL _ _ (HR Z hZ s hs).2.1 (HR W hW s hs).2.1).trans
      (mul_le_mul_of_nonneg_right hB (norm_nonneg _))
    have H2 := ((HD s hs).2 Z W hZ hW).trans
      (mul_le_mul_of_nonneg_right exp_one_quarter_lt_two.le (norm_nonneg _))
    have H3 := H1.trans (mul_le_mul_of_nonneg_left H2 hC0)
    convert! H3 using 1
    ring
  exact restartSectionMixedFlow_fderiv_comparison hC0 hh.le hb.1.le hbudget
    (fun s hs => (HR Z hZ s hs).1) (fun s hs => (HR W hW s hs).1)
    (Hjac Z hZ) (fun s hs => ((HD s hs).1 W hW).2.trans exp_one_quarter_lt_two.le) Hlip

end BianchiIX
