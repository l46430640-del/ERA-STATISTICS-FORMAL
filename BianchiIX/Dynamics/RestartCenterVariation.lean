import BianchiIX.Dynamics.RestartVariationComparison

noncomputable section

namespace BianchiIX

open Set

theorem restartCompactCenterProjection_comp_norm_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (L : E →L[ℝ] RestartState) :
    ‖restartCompactCenterProjection.comp L‖ ≤ ‖L‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg L)
  intro v
  exact (restartCompactCenterProjection_norm_le (L v)).trans (L.le_opNorm v)

theorem hasFDerivAt_restartSectionCenterFlow_of_mixed {h t : ℝ} {Z : RestartCenterState}
    (hh : 0 < h) (HD : DifferentiableAt ℝ (restartSectionMixedFlow h t) Z) :
    HasFDerivAt (restartSectionCenterFlow h t)
      (restartCompactCenterProjection.comp (fderiv ℝ (restartSectionMixedFlow h t) Z)) Z := by
  have H := restartCompactCenterProjection.hasFDerivAt.comp Z HD.hasFDerivAt
  simpa only [Function.comp_def, restartSectionMixedFlow_center hh] using H

theorem restartSectionRadicand_pos_of_small {h : ℝ} {Z : RestartCenterState}
    (hh : |h| ≤ 1 / 16) (hZ : ‖Z‖ ≤ 1 / 16) : 0 < restartSectionRadicand h Z := by
  have hw := restartPhysicalCoordinates_norm_le (x := restartSectionChart h Z) (by norm_num : (0 : ℝ) ≤ 1 / 16)
    hh (by rwa [restartCenterProjection_section])
  have H := (restartCompact_box_bounds hw).2.1
  change 246 / 256 ≤ restartSectionRadicand h Z at H
  linarith only [H]

theorem restartSectionCenterFlow_zero {h t : ℝ} (hh : h ^ 2 ≤ 1) (ht : 0 ≤ t) :
    restartSectionCenterFlow h t 0 = 0 := by
  have H := restartReferenceCurve_center_zero h (restartReferenceCurve_forward hh ht).1
  rw [restartSectionCenterFlow, restartSectionChart_zero]
  ext i
  fin_cases i
  · exact H.1
  · exact H.2.1
  · exact H.2.2

theorem restartSectionCenterFlow_fderiv_difference {h t : ℝ} {Z W : RestartCenterState}
    (hh : 0 < h) (HZ : DifferentiableAt ℝ (restartSectionMixedFlow h t) Z)
    (HW : DifferentiableAt ℝ (restartSectionMixedFlow h t) W) :
    ‖fderiv ℝ (restartSectionCenterFlow h t) Z - fderiv ℝ (restartSectionCenterFlow h t) W‖ ≤
      ‖fderiv ℝ (restartSectionMixedFlow h t) Z - fderiv ℝ (restartSectionMixedFlow h t) W‖ := by
  rw [(hasFDerivAt_restartSectionCenterFlow_of_mixed hh HZ).fderiv,
    (hasFDerivAt_restartSectionCenterFlow_of_mixed hh HW).fderiv]
  have heq : restartCompactCenterProjection.comp (fderiv ℝ (restartSectionMixedFlow h t) Z) -
      restartCompactCenterProjection.comp (fderiv ℝ (restartSectionMixedFlow h t) W) =
      restartCompactCenterProjection.comp
        (fderiv ℝ (restartSectionMixedFlow h t) Z - fderiv ℝ (restartSectionMixedFlow h t) W) := by
    ext v i
    simp
  rw [heq]
  exact restartCompactCenterProjection_comp_norm_le _

/-- Projecting the actual mixed flow retains the derivative comparison in the physical center variables. -/
theorem exists_restartSectionCenterFlow_derivative_comparison :
    ∃ C ≥ (32 : ℝ), ∀ (h b T : ℝ),
      0 < h → C * h ≤ 1 / 4 → (0 < b ∧ b ≤ 1 / 16) → 0 ≤ T → C * b * T ≤ 1 / 8 →
      ∀ t ∈ Icc (0 : ℝ) T,
        (∀ Z : RestartCenterState, ‖Z‖ ≤ b / 2 → DifferentiableAt ℝ (restartSectionCenterFlow h t) Z) ∧
        (∀ Z W : RestartCenterState, ‖Z‖ ≤ b / 2 → ‖W‖ ≤ b / 2 →
          ‖fderiv ℝ (restartSectionCenterFlow h t) Z - fderiv ℝ (restartSectionCenterFlow h t) W‖ ≤
            8 * C * t * ‖Z - W‖) := by
  obtain ⟨A, hA, HA⟩ := exists_restartSectionMixedFlow_derivative
  obtain ⟨B, _, HB⟩ := exists_restartSectionMixedFlow_fderiv_comparison
  let C := max A B
  have hAC : A ≤ C := le_max_left _ _
  have hBC : B ≤ C := le_max_right _ _
  refine ⟨C, hA.trans hAC, ?_⟩
  intro h b T hh hCh hb hT hCb t ht
  have HAh : A * h ≤ 1 / 4 := (mul_le_mul_of_nonneg_right hAC hh.le).trans hCh
  have HBh : B * h ≤ 1 / 4 := (mul_le_mul_of_nonneg_right hBC hh.le).trans hCh
  have HAT : A * b * T ≤ 1 / 8 :=
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hAC hb.1.le) hT).trans hCb
  have HBT : B * b * T ≤ 1 / 8 :=
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hBC hb.1.le) hT).trans hCb
  have HD := (HA h b T hh HAh hb hT HAT t ht).1
  refine ⟨fun Z hZ => (hasFDerivAt_restartSectionCenterFlow_of_mixed hh (HD Z hZ).1).differentiableAt, ?_⟩
  intro Z W hZ hW
  apply (restartSectionCenterFlow_fderiv_difference hh (HD Z hZ).1 (HD W hW).1).trans
  apply (HB h b T hh HBh hb hT HBT Z W hZ hW t ht).trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hBC (by norm_num)) ht.1) (norm_nonneg _)

end BianchiIX
