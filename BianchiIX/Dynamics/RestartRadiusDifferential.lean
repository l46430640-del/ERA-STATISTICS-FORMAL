import BianchiIX.Dynamics.RestartRadialVariation
import BianchiIX.Analysis.SquareRootRate

noncomputable section

namespace BianchiIX

open Set

def restartSectionRadiusRate (h t : ℝ) (Z : RestartCenterState) : ℝ :=
  restartSectionQuadraticRate h t Z / (2 * restartSectionRadius h t Z)

/-- The actual radial observable and its time rate have uniform ordinary initial derivatives. -/
theorem exists_restartSectionRadius_differential_bounds :
    ∃ C ≥ (32 : ℝ), ∀ c : ℝ, 0 < c → ∃ K : ℝ, 0 < K ∧
      ∀ (h b T : ℝ) (Z : RestartCenterState),
        0 < h → C * h ≤ 1 / 4 → (0 < b ∧ b ≤ 1 / 16) → 0 ≤ T → C * b * T ≤ 1 / 8 →
        ‖Z‖ ≤ b / 2 → c * b ≤ restartRadialNorm Z → ∀ t ∈ Icc (0 : ℝ) T,
          c * b / 2 ≤ restartSectionRadius h t Z ∧
          DifferentiableAt ℝ (restartSectionRadius h t) Z ∧
          ‖fderiv ℝ (restartSectionRadius h t) Z‖ ≤ K ∧
          DifferentiableAt ℝ (restartSectionRadiusRate h t) Z ∧
          ‖fderiv ℝ (restartSectionRadiusRate h t) Z‖ ≤
            K * (restartSectionStrongWall h t Z * b + b ^ 2) := by
  obtain ⟨A, hA, HA⟩ := exists_restartSectionQuadratic_control
  obtain ⟨B, _, HB⟩ := exists_restartSectionMixedFlow_derivative
  obtain ⟨D, hD, HD⟩ := exists_restartRadialQuadratic_fderiv_bound
  obtain ⟨E, hE, HE⟩ := exists_restartRadialDrift_tangent_bound
  let C := max A (max B (max D E))
  have hAC : A ≤ C := le_max_left _ _
  have hBC : B ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hDC : D ≤ C := ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hEC : E ≤ C := ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hC : 32 ≤ C := hA.trans hAC
  have hCpos : 0 < C := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 32) hC
  have hD0 : 0 ≤ D := le_trans (by norm_num : (0 : ℝ) ≤ 1) hD
  have hE0 : 0 ≤ E := le_trans (by norm_num : (0 : ℝ) ≤ 1) hE
  refine ⟨C, hC, ?_⟩
  intro c hc
  let K := (4 * C + (4 * C) ^ 2) / (c / 2)
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨K, hK, ?_⟩
  intro h b T Z hh hCh hb hT hCb hZ hradial t ht
  have hb0 : 0 ≤ b := hb.1.le
  have hsmall : h ≤ 1 / 16 := by nlinarith only [hC, hCh, hh]
  have hrad := restartSectionRadicand_pos_of_small (h := h) (Z := Z)
    (by rwa [abs_of_pos hh]) (by linarith only [hZ, hb.2])
  have Hheight (k : ℝ) (hk : k ≤ C) : k * h ≤ 1 / 4 :=
    (mul_le_mul_of_nonneg_right hk hh.le).trans hCh
  have Htime (k : ℝ) (hk : k ≤ C) : k * b * T ≤ 1 / 8 :=
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hk hb0) hT).trans hCb
  have H := HA h b T Z hh (Hheight A hAC) hb hT (Htime A hAC) hZ t ht
  have HM := (HB h b T hh (Hheight B hBC) hb hT (Htime B hBC) t ht).1 Z hZ
  have hn : 0 ≤ restartSectionStrongWall h t Z ∧ restartSectionStrongWall h t Z ≤ 1 / 16 :=
    ⟨H.1.le, H.2.2.1⟩
  have hn0 := hn.1
  have hn2 : restartSectionStrongWall h t Z ^ 2 < 1 := by nlinarith only [hn.1, hn.2]
  have Hcenter : ‖restartSectionCenterFlow h t Z‖ ≤ b := H.2.2.2.1
  have Hstate := restartSectionRadialState_derivative hh hrad ht.1 HM.1
    (HM.2.trans exp_one_quarter_lt_two.le) (by linarith only [hn.2])
  have HQfield : ‖fderiv ℝ restartRadialQuadratic (restartSectionRadialState h t Z)‖ ≤ C * b := by
    apply (HD _ _ (by rw [abs_of_nonneg hn.1]; exact hn.2) (Hcenter.trans hb.2)).trans
    exact mul_le_mul hDC Hcenter (norm_nonneg _) hCpos.le
  have HQ := restartSectionQuadratic_derivative_bound hCpos.le hb0 Hstate.1 Hstate.2.1 hn2 HQfield
  have HF := restartSectionQuadraticRate_derivative_bound hE0
    ⟨hb0, by linarith only [hb.2]⟩ Hstate.1 Hstate.2.1 Hstate.2.2 hn Hcenter
    (restartSectionRadicand_pos_of_small
      (by rw [abs_of_nonneg hn.1]; exact hn.2) (Hcenter.trans hb.2))
    (HE _ _ hn (Hcenter.trans hb.2))
  have Hlower : c * b / 2 ≤ restartSectionRadius h t Z := by
    have Hraw : restartRadialNorm Z ^ 2 = Z 0 ^ 2 + (Z 1 - Z 2) ^ 2 :=
      Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))
    have Hco := restartQuadratic_coercive ⟨hh.le, hsmall⟩ (Z 0) (Z 1 - Z 2)
    rw [← restartSectionQuadratic_initial h Z] at Hco
    have Hcb := mul_self_le_mul_self (mul_pos hc hb.1).le hradial
    have Hsq : restartSectionRadius h t Z ^ 2 = restartSectionQuadratic h t Z :=
      Real.sq_sqrt (restartSectionQuadratic_nonneg h t Z)
    have HR0 : 0 ≤ restartSectionRadius h t Z := Real.sqrt_nonneg _
    nlinarith only [Hraw, Hco, Hcb, Hsq, HR0, H.2.2.2.2.2.2.1, mul_pos hc hb.1]
  have HFval : |restartSectionQuadraticRate h t Z| ≤
      (4 * C) * (restartSectionStrongWall h t Z * b + b ^ 2) * restartSectionQuadratic h t Z := by
    apply H.2.2.2.2.2.1.trans
    gcongr
    · exact restartSectionQuadratic_nonneg h t Z
    · linarith only [hAC, hCpos]
  have HDF : ‖fderiv ℝ (restartSectionQuadraticRate h t) Z‖ ≤
      (4 * C) * (restartSectionStrongWall h t Z * b ^ 2 + b ^ 3) := by
    apply HF.2.trans
    gcongr
  have HDQ : ‖fderiv ℝ (restartSectionQuadratic h t) Z‖ ≤ (4 * C) * b :=
    HQ.2.trans (by nlinarith only [mul_nonneg hCpos.le hb0])
  have HR := sqrt_rate_derivative_bounds HQ.1 HF.1
    (by positivity : 0 ≤ 4 * C) (by positivity : 0 < c / 2) hb.1 hn.1
    (by change c / 2 * b ≤ restartSectionRadius h t Z; linarith only [Hlower]) HDQ HFval HDF
  have Hconst : (4 * C) / (c / 2) ≤ K :=
    div_le_div_of_nonneg_right (by nlinarith only [sq_nonneg (4 * C)]) (by positivity)
  exact ⟨Hlower, HR.1, HR.2.1.trans Hconst, HR.2.2.1, HR.2.2.2⟩

end BianchiIX
