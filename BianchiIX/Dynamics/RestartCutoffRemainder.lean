import BianchiIX.Dynamics.RestartRemainder

noncomputable section

namespace BianchiIX

open Set

/-- The explicit estimates (E.7) and the strong-wall bound hold for the same actual cutoff flow. -/
theorem exists_restartSection_cutoff_remainder :
    ∃ C ≥ (32 : ℝ), ∀ (h C₀ ρ q : ℝ),
      0 < h → C * h ≤ 1 / 4 → 0 < C₀ → (0 < ρ ∧ ρ ≤ 1) → 0 ≤ q →
      2 * C₀ * ρ ≤ 1 / 16 → C * (2 * C₀ * ρ) * (q / 2 * Real.log (1 / ρ)) ≤ 1 / 8 →
      ∀ Z : RestartCenterState, ‖Z‖ ≤ C₀ * ρ →
        let T := q / 2 * Real.log (1 / ρ)
        let x := normalizedMaxCurve (restartSectionChart h Z) 0 T
        T ∈ normalizedMaxDomain (restartSectionChart h Z) 0 ∧
        0 < x 2 ∧ x 2 ≤ h * ρ ^ q ∧
        restartSectionCenterFlow h T Z = restartCenterTransfer h Z + restartSectionRemainder h T Z ∧
        DifferentiableAt ℝ (restartSectionRemainder h T) Z ∧
        ‖restartSectionRemainder h T Z‖ ≤ 4 * C * C₀ ^ 2 * ρ ^ 2 * T + 6 * h * C₀ * ρ ^ (q + 1) ∧
        ‖fderiv ℝ (restartSectionRemainder h T) Z‖ ≤ 8 * C * C₀ * ρ * T + 6 * h * ρ ^ q := by
  obtain ⟨A, hA, HA⟩ := exists_restartSectionRemainder_bounds
  obtain ⟨B, _, HB⟩ := exists_restartSection_fastLayer_cutoff
  let C := max A B
  have hAC : A ≤ C := le_max_left _ _
  have hBC : B ≤ C := le_max_right _ _
  have hA0 : 0 ≤ A := le_trans (by norm_num : (0 : ℝ) ≤ 32) hA
  have hC0 : 0 ≤ C := hA0.trans hAC
  refine ⟨C, hA.trans hAC, ?_⟩
  intro h C₀ ρ q hh hCh hC₀ hρ hq hb hCb Z hZ
  have hρ0 : 0 < ρ := hρ.1
  let b := 2 * C₀ * ρ
  let T := q / 2 * Real.log (1 / ρ)
  have hb0 : 0 < b := by dsimp only [b]; positivity
  have hT : 0 ≤ T := mul_nonneg (div_nonneg hq (by norm_num))
    (Real.log_nonneg ((le_div_iff₀ hρ.1).mpr (by linarith only [hρ.2])))
  have hZb : ‖Z‖ ≤ b / 2 := by dsimp only [b]; linarith only [hZ]
  have HAh : A * h ≤ 1 / 4 := (mul_le_mul_of_nonneg_right hAC hh.le).trans hCh
  have HBh : B * h ≤ 1 / 4 := (mul_le_mul_of_nonneg_right hBC hh.le).trans hCh
  have HAT : A * b * T ≤ 1 / 8 :=
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hAC hb0.le) hT).trans hCb
  have HBT : B * b * T ≤ 1 / 8 :=
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hBC hb0.le) hT).trans hCb
  have HR := HA h b T hh HAh ⟨hb0, hb⟩ hT HAT T ⟨hT, le_rfl⟩ Z hZb
  have Hn := HB h b ρ q Z hh HBh ⟨hb0, hb⟩ hρ hq HBT hZb
  have hhsmall : h ≤ 1 / 16 := by
    nlinarith only [hCh, mul_le_mul_of_nonneg_right (hA.trans hAC) hh.le]
  have hrad := restartSectionRadicand_pos_of_small
    (by rwa [abs_of_pos hh]) (by linarith only [hZ, hb] : ‖Z‖ ≤ 1 / 16)
  have hdom := normalizedMaxDomain_contains_Ici_of_constraint (restartSectionChart_constraint hrad.le) 0 hT
  have he : Real.exp (-2 * T) = ρ ^ q := by
    rw [Real.rpow_def_of_pos hρ.1]
    congr 1
    dsimp only [T]
    rw [one_div, Real.log_inv]
    ring
  rw [he] at HR
  refine ⟨hdom, Hn.1, Hn.2.1, ?_, HR.1, ?_, ?_⟩
  · dsimp only [restartSectionRemainder]
    abel
  · apply HR.2.1.trans
    have H1 : 4 * A * T * ‖Z‖ ^ 2 ≤ 4 * C * T * (C₀ * ρ) ^ 2 := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hAC (by norm_num)) hT)
        ((sq_le_sq₀ (norm_nonneg Z) (mul_pos hC₀ hρ0).le).mpr hZ)
        (sq_nonneg _) (by positivity)
    have H2 : 6 * h * ρ ^ q * ‖Z‖ ≤ 6 * h * ρ ^ q * (C₀ * ρ) := by
      exact mul_le_mul_of_nonneg_left hZ (by positivity)
    exact (add_le_add H1 H2).trans_eq (by rw [Real.rpow_add hρ0, Real.rpow_one]; ring)
  · apply HR.2.2.trans
    have H1 : 8 * A * T * ‖Z‖ ≤ 8 * C * T * (C₀ * ρ) := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hAC (by norm_num)) hT)
        hZ (norm_nonneg _) (by positivity)
    calc
      8 * A * T * ‖Z‖ + 6 * h * ρ ^ q ≤ 8 * C * T * (C₀ * ρ) + 6 * h * ρ ^ q :=
        add_le_add H1 le_rfl
      _ = 8 * C * C₀ * ρ * T + 6 * h * ρ ^ q := by ring

end BianchiIX
