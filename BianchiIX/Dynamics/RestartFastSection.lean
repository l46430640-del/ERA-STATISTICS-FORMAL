import BianchiIX.Dynamics.RestartFastControl

noncomputable section

namespace BianchiIX

open Set

/-- The nonlinear control is uniform over a whole signed ball in the fixed physical section. -/
theorem exists_restartSection_fastLayer_control :
    ∃ C ≥ (32 : ℝ), ∀ (h b T : ℝ) (Z : RestartCenterState),
      0 < h → C * h ≤ 1 / 4 → (0 < b ∧ b ≤ 1 / 16) → 0 ≤ T →
      C * b * T ≤ 1 / 8 → ‖Z‖ ≤ b / 2 →
      ∀ t ∈ Icc (0 : ℝ) T,
        let x := normalizedMaxCurve (restartSectionChart h Z) 0 t
        0 < x 2 ∧ x 2 ≤ h * Real.exp (-2 * t) ∧ x 0 ≤ -(15 / 16) ∧
          ‖restartSectionCenterFlow h t Z‖ ≤ ‖Z‖ * Real.exp (restartFastBudget C h b t) ∧
          ‖restartSectionCenterFlow h t Z‖ < b := by
  obtain ⟨C, hC, HC⟩ := exists_normalized_restart_fastLayer_control
  refine ⟨C, hC, ?_⟩
  intro h b T Z hh hCh hb hT hCb hZ
  have hhsmall : h ≤ 1 / 128 := by
    nlinarith only [hCh, mul_le_mul_of_nonneg_right hC hh.le]
  let w : RestartState := ![h, Z 0, Z 1, Z 2]
  have hw : ‖w‖ ≤ 1 / 16 := by
    have hZsmall : ‖Z‖ ≤ 1 / 16 := by linarith only [hZ, hb.2]
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 16)).mpr
    intro i
    fin_cases i
    · change |h| ≤ 1 / 16
      rw [abs_of_pos hh]
      linarith only [hhsmall]
    · exact (norm_le_pi_norm Z 0).trans hZsmall
    · exact (norm_le_pi_norm Z 1).trans hZsmall
    · exact (norm_le_pi_norm Z 2).trans hZsmall
  have hr : 0 < restartSectionRadicand h Z := by
    have H := (restartCompact_box_bounds hw).2.1
    change 246 / 256 ≤ restartSectionRadicand h Z at H
    linarith only [H]
  have hp : restartSectionChart h Z 0 < 0 := neg_lt_zero.mpr (Real.sqrt_pos.mpr hr)
  have hbudget : C * h / 2 + C * b * T ≤ 1 / 4 := by linarith only [hCh, hCb]
  have H := HC h b T (restartSectionChart h Z) ⟨hh, hhsmall⟩ hb hT hbudget
    (restartSectionChart_constraint hr.le) hp ⟨hh, le_rfl⟩
    (by simpa only [restartCenterProjection_section] using hZ)
  intro t ht
  simpa only [restartCenterProjection_section, restartSectionCenterFlow] using H t ht

/-- The strong-wall part of (E.1) holds for every admissible nonzero center initial state. -/
theorem exists_restartSection_fastLayer_cutoff :
    ∃ C ≥ (32 : ℝ), ∀ (h b ρ q : ℝ) (Z : RestartCenterState),
      0 < h → C * h ≤ 1 / 4 → (0 < b ∧ b ≤ 1 / 16) →
      (0 < ρ ∧ ρ ≤ 1) → 0 ≤ q →
      C * b * (q / 2 * Real.log (1 / ρ)) ≤ 1 / 8 → ‖Z‖ ≤ b / 2 →
      let T := q / 2 * Real.log (1 / ρ)
      let x := normalizedMaxCurve (restartSectionChart h Z) 0 T
      0 < x 2 ∧ x 2 ≤ h * ρ ^ q ∧ x 0 ≤ -(15 / 16) ∧
        ‖restartSectionCenterFlow h T Z‖ ≤ ‖Z‖ * Real.exp (1 / 4) ∧
        ‖restartSectionCenterFlow h T Z‖ < b := by
  obtain ⟨C, hC, HC⟩ := exists_restartSection_fastLayer_control
  refine ⟨C, hC, ?_⟩
  intro h b ρ q Z hh hCh hb hρ hq hCb hZ
  let T := q / 2 * Real.log (1 / ρ)
  change C * b * T ≤ 1 / 8 at hCb
  have hlog : 0 ≤ Real.log (1 / ρ) :=
    Real.log_nonneg ((le_div_iff₀ hρ.1).mpr (by linarith only [hρ.2]))
  have hT : 0 ≤ T := mul_nonneg (div_nonneg hq (by norm_num)) hlog
  have he : Real.exp (-2 * T) = ρ ^ q := by
    rw [Real.rpow_def_of_pos hρ.1]
    congr 1
    dsimp only [T]
    rw [one_div, Real.log_inv]
    ring
  have H := HC h b T Z hh hCh hb hT hCb hZ T ⟨hT, le_rfl⟩
  have hbudget : restartFastBudget C h b T ≤ 1 / 4 :=
    (restartFastBudget_le (by linarith only [hC]) hh.le hb.1.le le_rfl).trans
      (by linarith only [hCh, hCb])
  refine ⟨H.1, ?_, H.2.2.1, ?_, H.2.2.2.2⟩
  · simpa only [he] using H.2.1
  · exact H.2.2.2.1.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hbudget) (norm_nonneg Z))

end BianchiIX
