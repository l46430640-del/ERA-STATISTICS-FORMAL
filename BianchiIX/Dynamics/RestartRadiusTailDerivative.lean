import BianchiIX.Dynamics.RestartGramDefect
import BianchiIX.Dynamics.RestartRadiusDifferential
import BianchiIX.Algebra.RestartRadialTail
import BianchiIX.Analysis.SquareRootDerivativeComparison

noncomputable section

namespace BianchiIX

open Set

def restartSectionRadiusTail (h t : ℝ) (Z : RestartCenterState) : ℝ :=
  restartSectionRadius h t Z - restartRadialNorm (restartSectionCenterFlow h t Z)

theorem restartSectionQuadraticDefect_derivative_bound {h t A b : ℝ} {Z : RestartCenterState}
    (hA : 0 ≤ A) (hb : 0 ≤ b ∧ b ≤ 1)
    (HD : DifferentiableAt ℝ (restartSectionRadialState h t) Z)
    (HB : ‖fderiv ℝ (restartSectionRadialState h t) Z‖ ≤ 2)
    (Hn : ∀ v : RestartCenterState,
      |(fderiv ℝ (restartSectionRadialState h t) Z v).1| ≤ 2 * restartSectionStrongWall h t Z * ‖v‖)
    (hn : 0 ≤ restartSectionStrongWall h t Z ∧ restartSectionStrongWall h t Z ≤ 1 / 16)
    (hcenter : ‖restartSectionCenterFlow h t Z‖ ≤ b)
    (HF : ∀ w : RestartRadialState,
      |fderiv ℝ restartRadialQuadraticDefect (restartSectionRadialState h t Z) w| ≤
        12 * A * |w.1| * ‖restartSectionCenterFlow h t Z‖ ^ 2 +
          24 * A * |restartSectionStrongWall h t Z| * ‖restartSectionCenterFlow h t Z‖ * ‖w.2‖) :
    ‖fderiv ℝ (fun W => restartRadialQuadraticDefect (restartSectionRadialState h t W)) Z‖ ≤
      72 * A * restartSectionStrongWall h t Z * b := by
  have hn0 := hn.1
  have hb0 := hb.1
  have hn2 : restartSectionStrongWall h t Z ^ 2 < 1 := by nlinarith only [hn.1, hn.2]
  have H := ((contDiffAt_restartRadialQuadraticDefect hn2 1).differentiableAt (by norm_num)).hasFDerivAt.comp Z HD.hasFDerivAt
  change HasFDerivAt (fun W => restartRadialQuadraticDefect (restartSectionRadialState h t W)) _ Z at H
  rw [H.fderiv]
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  have HW : ‖(fderiv ℝ (restartSectionRadialState h t) Z v).2‖ ≤ 2 * ‖v‖ :=
    (norm_snd_le _).trans (((fderiv ℝ (restartSectionRadialState h t) Z).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right HB (norm_nonneg _)))
  have Hsq : b ^ 2 ≤ b := by nlinarith only [mul_nonneg hb0 (sub_nonneg.mpr hb.2)]
  have Hraw := HF (fderiv ℝ (restartSectionRadialState h t) Z v)
  rw [abs_of_nonneg hn.1] at Hraw
  calc
    _ ≤ 12 * A * |(fderiv ℝ (restartSectionRadialState h t) Z v).1| * ‖restartSectionCenterFlow h t Z‖ ^ 2 +
        24 * A * restartSectionStrongWall h t Z * ‖restartSectionCenterFlow h t Z‖ *
          ‖(fderiv ℝ (restartSectionRadialState h t) Z v).2‖ := Hraw
    _ ≤ 12 * A * (2 * restartSectionStrongWall h t Z * ‖v‖) * b ^ 2 +
        24 * A * restartSectionStrongWall h t Z * b * (2 * ‖v‖) := by
      gcongr
      exact Hn v
    _ ≤ _ := by
      nlinarith only [mul_le_mul_of_nonneg_left Hsq
        (by positivity : 0 ≤ A * restartSectionStrongWall h t Z * ‖v‖)]

/-- The endpoint reference error has an ordinary initial derivative of order the actual strong wall. -/
theorem exists_restartSectionRadiusTail_derivative_bound :
    ∃ C ≥ (32 : ℝ), ∀ c : ℝ, 0 < c → ∃ K : ℝ, 0 < K ∧
      ∀ (h b T : ℝ) (Z : RestartCenterState),
        0 < h → C * h ≤ 1 / 4 → (0 < b ∧ b ≤ 1 / 16) → 0 ≤ T → C * b * T ≤ 1 / 8 →
        ‖Z‖ ≤ b / 2 → c * b ≤ restartRadialNorm Z → ∀ t ∈ Icc (0 : ℝ) T,
          DifferentiableAt ℝ (restartSectionRadiusTail h t) Z ∧
          ‖fderiv ℝ (restartSectionRadiusTail h t) Z‖ ≤ K * restartSectionStrongWall h t Z := by
  obtain ⟨A, hA, HA⟩ := exists_restartSectionQuadratic_control
  obtain ⟨B, _, HB⟩ := exists_restartSectionMixedFlow_derivative
  obtain ⟨D, hD, HD⟩ := exists_restartRadialQuadraticDefect_tangent_bound
  obtain ⟨E, _, HE⟩ := exists_restartRadialQuadratic_fderiv_bound
  let C := max A (max B (max D E))
  have hAC : A ≤ C := le_max_left _ _
  have hBC : B ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hDC : D ≤ C := ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hEC : E ≤ C := ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hC : 32 ≤ C := hA.trans hAC
  have hCpos : 0 < C := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 32) hC
  have hD0 : 0 ≤ D := le_trans (by norm_num : (0 : ℝ) ≤ 1) hD
  refine ⟨C, hC, ?_⟩
  intro c hc
  let K := (72 * C) / (c / 4) + (72 * C) ^ 2 / (c / 4) ^ 2
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨K, hK, ?_⟩
  intro h b T Z hh hCh hb hT hCb hZ hradial t ht
  have hbpos := hb.1
  have hb0 := hb.1.le
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
  have hnabs : |restartSectionStrongWall h t Z| ≤ 1 / 16 := by rw [abs_of_nonneg hn.1]; exact hn.2
  have hn2 : restartSectionStrongWall h t Z ^ 2 < 1 := by nlinarith only [hn.1, hn.2]
  have Hcenter : ‖restartSectionCenterFlow h t Z‖ ≤ b := H.2.2.2.1
  have Hstate := restartSectionRadialState_derivative hh hrad ht.1 HM.1
    (HM.2.trans exp_one_quarter_lt_two.le) (by linarith only [hn.2])
  have HQfield : ‖fderiv ℝ restartRadialQuadratic (restartSectionRadialState h t Z)‖ ≤ C * b :=
    (HE _ _ hnabs (Hcenter.trans hb.2)).trans (mul_le_mul hEC Hcenter (norm_nonneg _) hCpos.le)
  have HQ := restartSectionQuadratic_derivative_bound hCpos.le hb0 Hstate.1 Hstate.2.1 hn2 HQfield
  let S := fun W : RestartCenterState => restartSectionCenterFlow h t W 0 ^ 2 +
    (restartSectionCenterFlow h t W 1 - restartSectionCenterFlow h t W 2) ^ 2
  have HZdiff : DifferentiableAt ℝ (restartSectionCenterFlow h t) Z := Hstate.1.snd
  have HS : DifferentiableAt ℝ S Z := by dsimp only [S]; fun_prop
  have HSnonneg : 0 ≤ S Z := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have HlowerR : c * b / 2 ≤ restartSectionRadius h t Z := by
    have Hraw : restartRadialNorm Z ^ 2 = Z 0 ^ 2 + (Z 1 - Z 2) ^ 2 :=
      Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))
    have Hco := restartQuadratic_coercive ⟨hh.le, hsmall⟩ (Z 0) (Z 1 - Z 2)
    rw [← restartSectionQuadratic_initial h Z] at Hco
    have Hcb := mul_self_le_mul_self (mul_pos hc hb.1).le hradial
    have Hsq : restartSectionRadius h t Z ^ 2 = restartSectionQuadratic h t Z :=
      Real.sq_sqrt (restartSectionQuadratic_nonneg h t Z)
    have HR0 : 0 ≤ restartSectionRadius h t Z := Real.sqrt_nonneg _
    nlinarith only [Hraw, Hco, Hcb, Hsq, HR0, H.2.2.2.2.2.2.1, mul_pos hc hb.1]
  have HlowerS : c / 4 * b ≤ Real.sqrt (S Z) := by
    have Hupper := restartQuadratic_upper hn (restartSectionCenterFlow h t Z 0)
      (restartSectionCenterFlow h t Z 1 - restartSectionCenterFlow h t Z 2)
    change restartSectionQuadratic h t Z ≤ 2 * S Z at Hupper
    have Hsq : restartSectionRadius h t Z ^ 2 = restartSectionQuadratic h t Z :=
      Real.sq_sqrt (restartSectionQuadratic_nonneg h t Z)
    have HR0 : 0 ≤ restartSectionRadius h t Z := Real.sqrt_nonneg _
    have Hcmp : restartSectionRadius h t Z ≤ 2 * Real.sqrt (S Z) := by
      nlinarith only [Hupper, Hsq, Real.sq_sqrt HSnonneg, Real.sqrt_nonneg (S Z), HR0]
    linarith only [Hcmp, HlowerR]
  have Hvalue : |restartSectionRadius h t Z - Real.sqrt (S Z)| ≤ (72 * C) * restartSectionStrongWall h t Z * b := by
    have H1 : |restartSectionCenterFlow h t Z 1| ≤ b := (norm_le_pi_norm _ 1).trans Hcenter
    have H2 : |restartSectionCenterFlow h t Z 2| ≤ b := (norm_le_pi_norm _ 2).trans Hcenter
    have HV := sqrt_restartQuadratic_tail hn hb0 ((norm_le_pi_norm _ 0).trans Hcenter)
      (by linarith only [abs_sub (restartSectionCenterFlow h t Z 1) (restartSectionCenterFlow h t Z 2), H1, H2])
    exact HV.trans (by nlinarith only [mul_le_mul_of_nonneg_right hC (mul_nonneg hn0 hb0), mul_nonneg hn0 hb0])
  have Hdef := restartSectionQuadraticDefect_derivative_bound hD0
    ⟨hb0, by linarith only [hb.2]⟩ Hstate.1 Hstate.2.1 Hstate.2.2 hn Hcenter (HD _ _ hnabs)
  have HDS : ‖fderiv ℝ (fun W => restartSectionQuadratic h t W - S W) Z‖ ≤
      (72 * C) * restartSectionStrongWall h t Z * b := by
    apply Hdef.trans
    gcongr
  have HDQ : ‖fderiv ℝ (restartSectionQuadratic h t) Z‖ ≤ (72 * C) * b :=
    HQ.2.trans (by nlinarith only [mul_nonneg hCpos.le hb0])
  exact sqrt_sub_sqrt_derivative_bound HQ.1 HS (by positivity : 0 ≤ 72 * C)
    (by positivity : 0 < c / 4) hb.1 hn.1
    (by change c / 4 * b ≤ restartSectionRadius h t Z; nlinarith only [HlowerR, mul_pos hc hb.1])
    HlowerS Hvalue HDQ HDS

end BianchiIX
