import BianchiIX.Dynamics.ShearRestartCurves
import BianchiIX.Dynamics.RestartRadialCurveControl

noncomputable section

namespace BianchiIX

open Set

/-- Fixed weak-wall labels give time-linear, rather than inverse-scale, relative responses. -/
theorem exists_restartShearCurve_sharp_control :
    ∃ C ≥ (32 : ℝ), ∀ h a T : ℝ,
      0 < h → C * h ≤ 1 / 4 → (0 < a ∧ a ≤ 1) →
      8 * a ≤ 1 / 16 → 0 ≤ T → C * (8 * a) * T ≤ 1 / 8 →
      ∀ ε σ n₂ n₃ ρ : ℝ, (0 ≤ ε ∧ ε ≤ 1 / 64) → |σ| = 1 →
        (0 ≤ n₂ ∧ n₂ ≤ 2 * ε * a) → (0 ≤ n₃ ∧ n₃ ≤ 2 * ε * a) → ρ ∈ Icc a (2 * a) →
          let Z := restartShearCurve σ n₂ n₃ ρ
          let p := restartSectionRadialState h T Z
          let v := fderiv ℝ (restartSectionRadialState h T) Z (restartShearDirection σ)
          HasDerivAt (fun x => restartSectionRadialState h T (restartShearCurve σ n₂ n₃ x)) v ρ ∧
          normalizedMaxCurve (restartSectionChart h Z) 0 T 0 ≤ -(15 / 16) ∧
          0 < p.1 ∧ p.1 ≤ h * Real.exp (-2 * T) ∧ ‖p.2‖ ≤ 8 * a ∧
          ‖v‖ ≤ 2 ∧ |v.1| ≤ 2 * p.1 ∧
          ∀ i : Fin 2, Z i.succ / 2 ≤ p.2 i.succ ∧ p.2 i.succ ≤ 2 * Z i.succ ∧
            |v.2 i.succ| ≤ 8 * C * T * p.2 i.succ := by
  obtain ⟨A, _, HA⟩ := exists_restartSection_fastLayer_control
  obtain ⟨B, _, HB⟩ := exists_restartSectionMixedFlow_derivative
  obtain ⟨D, hD, HD⟩ := exists_restartSectionWeakWall_derivative
  let C := max A (max B D)
  have hAC : A ≤ C := le_max_left _ _
  have hBC : B ≤ C := (le_max_left B D).trans (le_max_right _ _)
  have hDC : D ≤ C := (le_max_right B D).trans (le_max_right _ _)
  have hC : 32 ≤ C := hD.trans hDC
  have hC₀ : 0 ≤ C := le_trans (by norm_num : (0 : ℝ) ≤ 32) hC
  refine ⟨C, hC, ?_⟩
  intro h a T hh hCh ha hb hT hCb ε σ n₂ n₃ ρ hε hσ h₂ h₃ hρ
  let b := 8 * a
  let Z := restartShearCurve σ n₂ n₃ ρ
  let p := restartSectionRadialState h T Z
  let v := fderiv ℝ (restartSectionRadialState h T) Z (restartShearDirection σ)
  have hbpos : 0 < b := by dsimp only [b]; positivity [ha.1]
  have hZ := (restartShearCurve_annulus ha.1 hρ hσ hε h₂ h₃).1
  have hZstrict : ‖Z‖ < b / 2 := by dsimp only [b]; linarith only [hZ, ha.1]
  have hbudget (E : ℝ) (hEC : E ≤ C) : E * h ≤ 1 / 4 ∧ E * b * T ≤ 1 / 8 :=
    ⟨(mul_le_mul_of_nonneg_right hEC hh.le).trans hCh,
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hEC hbpos.le) hT).trans hCb⟩
  have HF := HA h b T Z hh (hbudget A hAC).1 ⟨hbpos, hb⟩ hT (hbudget A hAC).2 hZstrict.le T ⟨hT, le_rfl⟩
  have HM := (HB h b T hh (hbudget B hBC).1 ⟨hbpos, hb⟩ hT (hbudget B hBC).2 T ⟨hT, le_rfl⟩).1 Z hZstrict.le
  have HW (i : Fin 2) := HD h b T hh (hbudget D hDC).1 ⟨hbpos, hb⟩ hT (hbudget D hDC).2 Z hZstrict i
  have hhsmall : h ≤ 1 / 16 := by nlinarith only [hCh, mul_le_mul_of_nonneg_right hC hh.le]
  have hrad := restartSectionRadicand_pos_of_small (h := h) (Z := Z)
    (by rwa [abs_of_pos hh]) (by linarith only [hZstrict.le, hb])
  have hn : restartSectionStrongWall h T Z ≤ 1 := by
    have Hexp : Real.exp (-2 * T) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith only [hT])
    change normalizedMaxCurve (restartSectionChart h Z) 0 T 2 ≤ 1
    exact HF.2.1.trans ((mul_le_mul_of_nonneg_left Hexp hh.le).trans (by linarith only [hhsmall]))
  have HS := restartSectionRadialState_derivative hh hrad hT HM.1 (HM.2.trans exp_one_quarter_lt_two.le) hn
  have Hcurve := HS.1.hasFDerivAt.comp_hasDerivAt ρ (hasDerivAt_restartShearCurve σ n₂ n₃ ρ)
  have hvnorm : ‖v‖ ≤ 2 := by
    have H := (fderiv ℝ (restartSectionRadialState h T) Z).le_opNorm (restartShearDirection σ)
    rw [restartShearDirection_norm hσ, mul_one] at H
    exact H.trans HS.2.1
  have hnpos : 0 < p.1 := HF.1
  refine ⟨Hcurve, HF.2.2.1, hnpos, HF.2.1, HF.2.2.2.2.le, hvnorm, ?_, ?_⟩
  · have H := HS.2.2 (restartShearDirection σ)
    rw [restartShearDirection_norm hσ, mul_one] at H
    exact H
  · intro i
    have hZi : 0 ≤ Z i.succ := by fin_cases i; exact h₂.1; exact h₃.1
    have hformula : p.2 i.succ = Z i.succ * restartSectionWeakMultiplier h T i Z := (HW i).1
    have hpi : 0 ≤ p.2 i.succ := by
      rw [hformula]
      exact mul_nonneg hZi (by linarith only [(HW i).2.1.1])
    change Z i.succ / 2 ≤ p.2 i.succ ∧ p.2 i.succ ≤ 2 * Z i.succ ∧
      |v.2 i.succ| ≤ 8 * C * T * p.2 i.succ
    refine ⟨?_, ?_, ?_⟩
    · rw [hformula]
      nlinarith only [mul_le_mul_of_nonneg_left (HW i).2.1.1.le hZi]
    · rw [hformula]
      nlinarith only [mul_le_mul_of_nonneg_left (HW i).2.1.2.le hZi]
    · have H := (HW i).2.2.2 (restartShearDirection σ) (by fin_cases i <;> rfl)
      rw [restartSectionRadialState_center_fderiv HS.1, restartShearDirection_norm hσ, mul_one] at H
      change |v.2 i.succ| ≤ 8 * D * T * |p.2 i.succ| at H
      rw [abs_of_nonneg hpi] at H
      exact H.trans (by gcongr)

/-- The coarser inverse-scale estimate follows from the sharp bound when the fast-time budget holds. -/
theorem exists_restartShearCurve_control :
    ∃ C ≥ (32 : ℝ), ∀ h a T : ℝ,
      0 < h → C * h ≤ 1 / 4 → (0 < a ∧ a ≤ 1) →
      8 * a ≤ 1 / 16 → 0 ≤ T → C * (8 * a) * T ≤ 1 / 8 → a * T ≤ 1 →
      ∀ ε σ n₂ n₃ ρ : ℝ, (0 ≤ ε ∧ ε ≤ 1 / 64) → |σ| = 1 →
        (0 ≤ n₂ ∧ n₂ ≤ 2 * ε * a) → (0 ≤ n₃ ∧ n₃ ≤ 2 * ε * a) → ρ ∈ Icc a (2 * a) →
          let Z := restartShearCurve σ n₂ n₃ ρ
          let p := restartSectionRadialState h T Z
          let v := fderiv ℝ (restartSectionRadialState h T) Z (restartShearDirection σ)
          HasDerivAt (fun x => restartSectionRadialState h T (restartShearCurve σ n₂ n₃ x)) v ρ ∧
          normalizedMaxCurve (restartSectionChart h Z) 0 T 0 ≤ -(15 / 16) ∧
          0 < p.1 ∧ p.1 ≤ h * Real.exp (-2 * T) ∧ ‖p.2‖ ≤ 8 * a ∧
          ‖v‖ ≤ 2 ∧ |v.1| ≤ 2 * p.1 / a ∧
          ∀ i : Fin 2, Z i.succ / 2 ≤ p.2 i.succ ∧ p.2 i.succ ≤ 2 * Z i.succ ∧
            |v.2 i.succ| ≤ 8 * C * p.2 i.succ / a := by
  obtain ⟨C, hC, HC⟩ := exists_restartShearCurve_sharp_control
  refine ⟨C, hC, ?_⟩
  intro h a T hh hCh ha hb hT hCb haT ε σ n₂ n₃ ρ hε hσ h₂ h₃ hρ Z p v
  obtain ⟨Hcurve, hp, hn, hne, hcenter, hv, hnv, HW⟩ :=
    HC h a T hh hCh ha hb hT hCb ε σ n₂ n₃ ρ hε hσ h₂ h₃ hρ
  refine ⟨Hcurve, hp, hn, hne, hcenter, hv, ?_, ?_⟩
  · apply (le_div_iff₀ ha.1).mpr
    nlinarith only [mul_le_mul_of_nonneg_right hnv ha.1.le,
      mul_le_mul_of_nonneg_left ha.2 hn.le]
  · intro i
    have hZi : 0 ≤ Z i.succ := by fin_cases i; exact h₂.1; exact h₃.1
    have hpi : 0 ≤ p.2 i.succ := (div_nonneg hZi (by norm_num)).trans (HW i).1
    refine ⟨(HW i).1, (HW i).2.1, (le_div_iff₀ ha.1).mpr ?_⟩
    have HT := mul_le_mul_of_nonneg_left haT
      (show 0 ≤ 8 * C * p.2 i.succ by positivity [le_trans (by norm_num : (0 : ℝ) ≤ 32) hC])
    nlinarith only [mul_le_mul_of_nonneg_right (HW i).2.2 ha.1.le, HT]

end BianchiIX
