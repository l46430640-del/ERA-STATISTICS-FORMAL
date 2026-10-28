import BianchiIX.Dynamics.RestartWeakMultiplierBounds

noncomputable section

namespace BianchiIX

def restartSectionWeakMultiplier (h T : ℝ) (i : Fin 2) (Z : RestartCenterState) : ℝ :=
  restartWeakMultiplier T i (restartMixedSection h Z)

def restartSectionWeakLogMultiplier (h T : ℝ) (i : Fin 2) (Z : RestartCenterState) : ℝ :=
  restartWeakLogMultiplier T i (restartMixedSection h Z)

theorem restartSectionWeakLogMultiplier_eq_log (h T : ℝ) (i : Fin 2) (Z : RestartCenterState) :
    restartSectionWeakLogMultiplier h T i Z = Real.log (restartSectionWeakMultiplier h T i Z) :=
  restartWeakLogMultiplier_eq_log T i (restartMixedSection h Z)

theorem contDiff_restartMixedSection (h : ℝ) (k : WithTop ℕ∞) :
    ContDiff ℝ k (restartMixedSection h) := by
  rw [contDiff_pi]
  intro i
  fin_cases i
  · exact contDiff_const
  · exact contDiff_apply ℝ ℝ (0 : Fin 3)
  · exact contDiff_apply ℝ ℝ (1 : Fin 3)
  · exact contDiff_apply ℝ ℝ (2 : Fin 3)

theorem fderiv_comp_restartMixedSection_norm_le {f : RestartState → ℝ}
    {h : ℝ} {Z : RestartCenterState} (H : DifferentiableAt ℝ f (restartMixedSection h Z)) :
    ‖fderiv ℝ (fun W => f (restartMixedSection h W)) Z‖ ≤ ‖fderiv ℝ f (restartMixedSection h Z)‖ := by
  have HD := H.hasFDerivAt.comp Z (hasFDerivAt_restartMixedSection h Z)
  change HasFDerivAt (fun W => f (restartMixedSection h W)) _ Z at HD
  rw [HD.fderiv]
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro v
  change ‖fderiv ℝ f (restartMixedSection h Z) (restartCenterInclusion v)‖ ≤ _
  simpa only [restartCenterInclusion_norm] using
    (fderiv ℝ f (restartMixedSection h Z)).le_opNorm (restartCenterInclusion v)

/-- The positive weak factors and their ordinary derivatives on the physical fixed-height section. -/
theorem exists_restartSectionWeakMultiplier_bounds :
    ∃ C ≥ (32 : ℝ), ∀ (h b T : ℝ),
      0 < h → C * h ≤ 1 / 4 → (0 < b ∧ b ≤ 1 / 16) → 0 ≤ T → C * b * T ≤ 1 / 8 →
      ∀ Z : RestartCenterState, ‖Z‖ ≤ b / 2 → ∀ i : Fin 2,
        normalizedMaxCurve (restartSectionChart h Z) 0 T (i.addNat 3) =
          Z i.succ * restartSectionWeakMultiplier h T i Z ∧
        |restartSectionWeakLogMultiplier h T i Z| ≤ 1 / 4 ∧
        (1 / 2 < restartSectionWeakMultiplier h T i Z ∧ restartSectionWeakMultiplier h T i Z < 2) ∧
        (restartSectionWeakMultiplier h T i Z)⁻¹ < 2 ∧
        ContDiffAt ℝ 2 (restartSectionWeakLogMultiplier h T i) Z ∧
        ContDiffAt ℝ 2 (restartSectionWeakMultiplier h T i) Z ∧
        ‖fderiv ℝ (restartSectionWeakLogMultiplier h T i) Z‖ ≤ 2 * C * T ∧
        ‖fderiv ℝ (restartSectionWeakMultiplier h T i) Z‖ ≤ 4 * C * T := by
  obtain ⟨C, hC, HC⟩ := exists_restartWeakMultiplier_bounds
  refine ⟨C, hC, ?_⟩
  intro h b T hh hCh hb hT hCb Z hZ i
  have H := HC h b T (restartMixedSection h Z) hh hCh hb hT hCb
    (by change Real.exp (Real.log h) ≤ h; rw [Real.exp_log hh])
    (by rwa [restartMixedSection_center]) i
  obtain ⟨Hformula, Hlog, Hbounds, Hinv, Hlogreg, Hreg, HlogD, HD⟩ := H
  have Hsection := (contDiff_restartMixedSection h 2).contDiffAt (x := Z)
  refine ⟨?_, Hlog, Hbounds, Hinv, Hlogreg.comp Z Hsection, Hreg.comp Z Hsection, ?_, ?_⟩
  · change restartSectionMixedFlow h T Z (i.addNat 2) = _ at Hformula
    rw [restartSectionMixedFlow_physical hh] at Hformula
    fin_cases i <;> exact Hformula
  · exact (fderiv_comp_restartMixedSection_norm_le (Hlogreg.differentiableAt (by norm_num))).trans HlogD
  · exact (fderiv_comp_restartMixedSection_norm_le (Hreg.differentiableAt (by norm_num))).trans HD

end BianchiIX
