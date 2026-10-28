import BianchiIX.Dynamics.RestartCenterVariation
import BianchiIX.Analysis.RadialRemainder

noncomputable section

namespace BianchiIX

open Set

/-- The exact center flow minus its limiting linear transfer, at fixed height and time. -/
def restartSectionRemainder (h t : ℝ) (Z : RestartCenterState) : RestartCenterState :=
  restartSectionCenterFlow h t Z - restartCenterTransfer h Z

theorem hasFDerivAt_restartSectionRemainder {h t : ℝ} {Z : RestartCenterState}
    (HD : DifferentiableAt ℝ (restartSectionCenterFlow h t) Z) :
    HasFDerivAt (restartSectionRemainder h t)
      (fderiv ℝ (restartSectionCenterFlow h t) Z - restartCenterTransfer h) Z :=
  HD.hasFDerivAt.sub (restartCenterTransfer h).hasFDerivAt

theorem restartSectionRemainder_zero {h t : ℝ} (hh : h ^ 2 ≤ 1) (ht : 0 ≤ t) :
    restartSectionRemainder h t 0 = 0 := by
  rw [restartSectionRemainder, restartSectionCenterFlow_zero hh ht, map_zero, sub_self]

/-- The actual derivative comparison and reference tail give both nonlinear remainder bounds. -/
theorem restartSectionRemainder_bounds {C h b t : ℝ}
    (hh : 0 < h ∧ h ≤ 1 / 16) (ht : 0 ≤ t)
    (HD : ∀ Z : RestartCenterState, ‖Z‖ ≤ b / 2 → DifferentiableAt ℝ (restartSectionCenterFlow h t) Z)
    (HJ : ∀ Z : RestartCenterState, ‖Z‖ ≤ b / 2 →
      ‖fderiv ℝ (restartSectionCenterFlow h t) Z - fderiv ℝ (restartSectionCenterFlow h t) 0‖ ≤
        8 * C * t * ‖Z‖) :
    ∀ Z : RestartCenterState, ‖Z‖ ≤ b / 2 →
      DifferentiableAt ℝ (restartSectionRemainder h t) Z ∧
      ‖restartSectionRemainder h t Z‖ ≤ 4 * C * t * ‖Z‖ ^ 2 + 6 * h * Real.exp (-2 * t) * ‖Z‖ ∧
      ‖fderiv ℝ (restartSectionRemainder h t) Z‖ ≤ 8 * C * t * ‖Z‖ + 6 * h * Real.exp (-2 * t) := by
  have hh2 : h ^ 2 < 1 := by nlinarith only [hh.1, hh.2]
  have Href : fderiv ℝ (restartSectionCenterFlow h t) 0 = restartReferenceCenterDifferential h t :=
    (hasFDerivAt_restartSectionCenterFlow_zero hh2 ht).fderiv
  have Htail := (restartReferenceCenterDifferential_bounds hh ht).2
  have HR (Z : RestartCenterState) (hZ : ‖Z‖ ≤ b / 2) :
      ‖fderiv ℝ (restartSectionRemainder h t) Z‖ ≤ 8 * C * t * ‖Z‖ + 6 * h * Real.exp (-2 * t) := by
    rw [(hasFDerivAt_restartSectionRemainder (HD Z hZ)).fderiv]
    exact (norm_sub_le_norm_sub_add_norm_sub _ (fderiv ℝ (restartSectionCenterFlow h t) 0) _).trans
      (add_le_add (HJ Z hZ) (by simpa only [Href] using Htail))
  intro Z hZ
  have Hθ (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) 1) : ‖θ • Z‖ ≤ b / 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hθ.1]
    exact (mul_le_mul_of_nonneg_right hθ.2 (norm_nonneg Z)).trans (by simpa only [one_mul] using hZ)
  have Hvalue := norm_le_quadratic_of_radial_fderiv
    (restartSectionRemainder_zero hh2.le ht)
    (fun θ hθ => (hasFDerivAt_restartSectionRemainder (HD (θ • Z) (Hθ θ hθ))).differentiableAt)
    (A := 8 * C * t) (B := 6 * h * Real.exp (-2 * t)) (x := Z) (fun θ hθ => by
      have H := HR (θ • Z) (Hθ θ hθ)
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hθ.1] at H
      convert! H using 1
      ring)
  refine ⟨(hasFDerivAt_restartSectionRemainder (HD Z hZ)).differentiableAt, ?_, HR Z hZ⟩
  convert! Hvalue using 1
  ring

/-- Finite-time nonlinear control uses only the section, initial amplitude, and integrated budget. -/
theorem exists_restartSectionRemainder_bounds :
    ∃ C ≥ (32 : ℝ), ∀ (h b T : ℝ),
      0 < h → C * h ≤ 1 / 4 → (0 < b ∧ b ≤ 1 / 16) → 0 ≤ T → C * b * T ≤ 1 / 8 →
      ∀ t ∈ Icc (0 : ℝ) T, ∀ Z : RestartCenterState, ‖Z‖ ≤ b / 2 →
        DifferentiableAt ℝ (restartSectionRemainder h t) Z ∧
        ‖restartSectionRemainder h t Z‖ ≤ 4 * C * t * ‖Z‖ ^ 2 + 6 * h * Real.exp (-2 * t) * ‖Z‖ ∧
        ‖fderiv ℝ (restartSectionRemainder h t) Z‖ ≤ 8 * C * t * ‖Z‖ + 6 * h * Real.exp (-2 * t) := by
  obtain ⟨C, hC, HC⟩ := exists_restartSectionCenterFlow_derivative_comparison
  refine ⟨C, hC, ?_⟩
  intro h b T hh hCh hb hT hCb t ht
  have hhsmall : h ≤ 1 / 16 := by
    nlinarith only [hCh, mul_le_mul_of_nonneg_right hC hh.le]
  have H := HC h b T hh hCh hb hT hCb t ht
  apply restartSectionRemainder_bounds ⟨hh, hhsmall⟩ ht.1 H.1
  intro Z hZ
  simpa only [sub_zero] using H.2 Z 0 hZ (by simpa only [norm_zero] using half_pos hb.1 |>.le)

end BianchiIX
