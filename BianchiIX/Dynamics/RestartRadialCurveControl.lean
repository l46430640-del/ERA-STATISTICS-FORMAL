import BianchiIX.Dynamics.RestartSectionWeakDerivative
import BianchiIX.Dynamics.RestartRadialCurves

noncomputable section

namespace BianchiIX

open Set

theorem restartSectionRadialState_center_fderiv {h T : ℝ} {Z : RestartCenterState}
    (H : DifferentiableAt ℝ (restartSectionRadialState h T) Z) (i : Fin 3) (v : RestartCenterState) :
    fderiv ℝ (fun W => restartSectionCenterFlow h T W i) Z v =
      (fderiv ℝ (restartSectionRadialState h T) Z v).2 i := by
  have HD := (ContinuousLinearMap.proj i).hasFDerivAt.comp Z
    ((ContinuousLinearMap.snd ℝ ℝ RestartCenterState).hasFDerivAt.comp Z H.hasFDerivAt)
  change HasFDerivAt (fun W => restartSectionCenterFlow h T W i) _ Z at HD
  rw [HD.fderiv]
  rfl

/-- All amplitude and tangent bounds needed by the projection comparison hold on actual radial curves. -/
theorem exists_restartRadialCurve_control :
    ∃ C ≥ (32 : ℝ), ∀ h r T L : ℝ,
      0 < h → C * h ≤ 1 / 4 → (0 < r ∧ r ≤ 1) → 0 ≤ L →
      8 * (L + 1) * r ≤ 1 / 16 → 0 ≤ T → C * (8 * (L + 1) * r) * T ≤ 1 / 8 → r * T ≤ 1 →
      ∀ θ ζ ρ : ℝ, |θ| ≤ L → (0 ≤ ζ ∧ ζ ≤ r / 9) → ρ ∈ Icc r (2 * r) →
        let Z := restartRadialCurve θ ζ ρ
        let p := restartSectionRadialState h T Z
        let v := fderiv ℝ (restartSectionRadialState h T) Z (restartRadialDirection θ)
        HasDerivAt (fun x => restartSectionRadialState h T (restartRadialCurve θ ζ x)) v ρ ∧
        normalizedMaxCurve (restartSectionChart h Z) 0 T 0 ≤ -(15 / 16) ∧
        0 < p.1 ∧ p.1 ≤ h * Real.exp (-2 * T) ∧
        ‖p.2‖ ≤ 8 * (L + 1) * r ∧ r / 2 ≤ p.2 1 ∧
        (0 ≤ p.2 2 ∧ p.2 2 ≤ 2 * ζ) ∧
        (∀ i : Fin 3, |v.2 i| ≤ 2 * (L + 1)) ∧
        |v.1| ≤ 2 * (L + 1) * p.1 / r ∧
        |v.2 2| ≤ 8 * C * (L + 1) * p.2 2 / r := by
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
  intro h r T L hh hCh hr hL hb hT hCb hrT θ ζ ρ hθ hζ hρ
  let b := 8 * (L + 1) * r
  let Z := restartRadialCurve θ ζ ρ
  let p := restartSectionRadialState h T Z
  let v := fderiv ℝ (restartSectionRadialState h T) Z (restartRadialDirection θ)
  have hbpos : 0 < b := by dsimp only [b]; positivity [hr.1]
  have hZ := (restartRadialCurve_annulus hr.1 hρ hL hθ hζ).1
  have hZstrict : ‖Z‖ < b / 2 := by
    change ‖Z‖ ≤ 2 * (L + 1) * r at hZ
    dsimp only [b]
    nlinarith only [hZ, mul_pos (show 0 < L + 1 by positivity) hr.1]
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
  have Hcurve := HS.1.hasFDerivAt.comp_hasDerivAt ρ (hasDerivAt_restartRadialCurve θ ζ ρ)
  have hvnorm : ‖v‖ ≤ 2 * (L + 1) := by
    exact ((fderiv ℝ (restartSectionRadialState h T) Z).le_opNorm _).trans
      (mul_le_mul HS.2.1 (restartRadialDirection_norm_le hL hθ) (norm_nonneg _) (by norm_num))
  have Hactive : p.2 1 = ρ * restartSectionWeakMultiplier h T 0 Z := (HW 0).1
  have Hweak : p.2 2 = ζ * restartSectionWeakMultiplier h T 1 Z := (HW 1).1
  have hweakpos : 0 ≤ p.2 2 := by
    rw [Hweak]
    exact mul_nonneg hζ.1 (by linarith only [(HW 1).2.1.1])
  have hnpos : 0 < p.1 := HF.1
  refine ⟨Hcurve, HF.2.2.1, hnpos, HF.2.1, HF.2.2.2.2.le, ?_, ⟨hweakpos, ?_⟩, ?_, ?_, ?_⟩
  · have H := mul_le_mul_of_nonneg_left (HW 0).2.1.1.le (hr.1.trans_le hρ.1).le
    rw [Hactive]
    nlinarith only [H, hρ.1]
  · rw [Hweak]
    nlinarith only [mul_le_mul_of_nonneg_left (HW 1).2.1.2.le hζ.1]
  · intro i
    exact (norm_le_pi_norm v.2 i).trans ((norm_snd_le v).trans hvnorm)
  · have H := (HS.2.2 (restartRadialDirection θ)).trans
      (mul_le_mul_of_nonneg_left (restartRadialDirection_norm_le hL hθ) (by positivity : 0 ≤ 2 * p.1))
    change |v.1| ≤ 2 * p.1 * (L + 1) at H
    apply (le_div_iff₀ hr.1).mpr
    have H' := mul_le_mul_of_nonneg_right H hr.1.le
    nlinarith only [H', mul_le_mul_of_nonneg_left hr.2 (show 0 ≤ 2 * p.1 * (L + 1) by positivity)]
  · have H := (HW 1).2.2.2 (restartRadialDirection θ) (by rfl)
    rw [restartSectionRadialState_center_fderiv HS.1] at H
    change |v.2 2| ≤ 8 * D * T * |p.2 2| * ‖restartRadialDirection θ‖ at H
    rw [abs_of_nonneg hweakpos] at H
    have Hbound : |v.2 2| ≤ 8 * C * T * p.2 2 * (L + 1) := H.trans (by
      gcongr
      exact restartRadialDirection_norm_le hL hθ)
    apply (le_div_iff₀ hr.1).mpr
    have H' := mul_le_mul_of_nonneg_right Hbound hr.1.le
    have HT := mul_le_mul_of_nonneg_left hrT (show 0 ≤ 8 * C * p.2 2 * (L + 1) by positivity)
    nlinarith only [H', HT]

end BianchiIX
