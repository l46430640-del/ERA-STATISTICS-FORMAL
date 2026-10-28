import BianchiIX.Dynamics.RestartRadialDrift

noncomputable section

namespace BianchiIX

/-- All three bounds of (E.10), with ordinary partial derivatives and one fixed constant. -/
theorem exists_restartRadialDrift_bounds :
    ∃ C ≥ (1 : ℝ), ∀ (n : ℝ) (Z : RestartCenterState),
      (0 ≤ n ∧ n ≤ 1 / 16) → ‖Z‖ ≤ 1 / 16 →
      ContDiffAt ℝ 3 restartRadialDrift (n, Z) ∧
      |restartRadialDrift (n, Z)| ≤ C * (n * ‖Z‖ + ‖Z‖ ^ 2) * restartQuadratic n (Z 0) (Z 1 - Z 2) ∧
      ‖fderiv ℝ (fun W => restartRadialDrift (n, W)) Z‖ ≤ C * (n * ‖Z‖ ^ 2 + ‖Z‖ ^ 3) ∧
      |deriv (fun m => restartRadialDrift (m, Z)) n| ≤ C * ‖Z‖ ^ 3 := by
  obtain ⟨A, hA, HA⟩ := exists_restartRadialDriftCoefficients_bounds
  have hA0 : 0 ≤ A := le_trans (by norm_num : (0 : ℝ) ≤ 1) hA
  refine ⟨36 * A, by linarith only [hA], ?_⟩
  intro n Z hn hZ
  have hnabs : |n| ≤ 1 / 16 := by rw [abs_of_nonneg hn.1]; exact hn.2
  have hn2 : n ^ 2 < 1 := by nlinarith only [hn.1, hn.2]
  have hrad := restartSectionRadicand_pos_of_small hnabs hZ
  have Hreg := contDiffAt_restartRadialDrift (p := (n, Z)) hn2 hrad
  have HM := HA n Z hnabs hZ
  rw [abs_of_nonneg hn.1] at HM
  have hQ0 : 0 ≤ restartQuadratic n (Z 0) (Z 1 - Z 2) := add_nonneg (sq_nonneg _) (sq_nonneg _)
  refine ⟨Hreg, ?_, ?_, ?_⟩
  · apply (abs_quadraticFromCoefficients_le (restartRadialDriftCoefficients (n, Z)) (Z 0) (Z 1 - Z 2)).trans
    have Hco := restartQuadratic_coercive hn (Z 0) (Z 1 - Z 2)
    calc
      _ ≤ 2 * (A * (n + ‖Z‖) * ‖Z‖) * (2 * restartQuadratic n (Z 0) (Z 1 - Z 2)) := by
        gcongr
        · positivity [hn.1]
        · exact HM.1
      _ ≤ 36 * A * (n * ‖Z‖ + ‖Z‖ ^ 2) * restartQuadratic n (Z 0) (Z 1 - Z 2) := by
        nlinarith only [mul_nonneg
          (mul_nonneg (mul_nonneg hA0 (add_nonneg hn.1 (norm_nonneg Z))) (norm_nonneg Z)) hQ0]
  · have HD := (Hreg.differentiableAt (by norm_num)).hasFDerivAt.comp Z
      (hasFDerivAt_prodMk_right (𝕜 := ℝ) n Z)
    change HasFDerivAt (fun W => restartRadialDrift (n, W)) _ Z at HD
    rw [HD.fderiv]
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity [hn.1])
    intro W
    change |fderiv ℝ restartRadialDrift (n, Z) (0, W)| ≤ _
    have HV : ‖fderiv ℝ restartRadialDriftCoefficients (n, Z) (0, W)‖ ≤ A * (n + ‖Z‖) * ‖W‖ := by
      simpa using ((fderiv ℝ restartRadialDriftCoefficients (n, Z)).le_opNorm (0, W)).trans
        (mul_le_mul_of_nonneg_right HM.2.1 (norm_nonneg (0, W)))
    calc
      _ ≤ 12 * ‖fderiv ℝ restartRadialDriftCoefficients (n, Z) (0, W)‖ * ‖Z‖ ^ 2 +
          24 * ‖restartRadialDriftCoefficients (n, Z)‖ * ‖Z‖ * ‖W‖ :=
        abs_fderiv_restartRadialDrift_apply_le (p := (n, Z)) hn2 hrad (0, W)
      _ ≤ 12 * (A * (n + ‖Z‖) * ‖W‖) * ‖Z‖ ^ 2 +
          24 * (A * (n + ‖Z‖) * ‖Z‖) * ‖Z‖ * ‖W‖ := by
        gcongr
        exact HM.1
      _ = _ := by ring
  · have HD := (Hreg.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt n
      ((hasDerivAt_id' n).prodMk (hasDerivAt_const n Z))
    change HasDerivAt (fun m => restartRadialDrift (m, Z)) _ n at HD
    rw [HD.deriv]
    have H := abs_fderiv_restartRadialDrift_apply_le (p := (n, Z)) hn2 hrad (1, 0)
    change |fderiv ℝ restartRadialDrift (n, Z) (1, 0)| ≤ _ at H
    simp only [norm_zero, mul_zero, add_zero] at H
    calc
      _ ≤ 12 * ‖fderiv ℝ restartRadialDriftCoefficients (n, Z) (1, 0)‖ * ‖Z‖ ^ 2 := H
      _ ≤ 12 * (A * ‖Z‖) * ‖Z‖ ^ 2 := by gcongr; exact HM.2.2
      _ ≤ 36 * A * ‖Z‖ ^ 3 := by nlinarith only [mul_nonneg hA0 (pow_nonneg (norm_nonneg Z) 3)]

end BianchiIX
