import BianchiIX.Analysis.RestartDriftCoefficientBounds
import BianchiIX.Algebra.RestartQuadraticBounds

noncomputable section

namespace BianchiIX

def restartRadialDrift (p : RestartRadialState) : ℝ :=
  quadraticFromCoefficients (restartRadialDriftCoefficients p) (p.2 0) (p.2 1 - p.2 2)

theorem restartRadialDrift_formula {p : RestartRadialState} (hn : p.1 ^ 2 < 1) :
    restartRadialDrift p =
      p.1 * (restartRadialCurvatureDifference p - 2 * restartRadialRootDifference p) *
        restartQuadraticStrongDerivative p.1 (p.2 0) (p.2 1 - p.2 2) +
      2 * restartRadialCurvatureDifference p * restartQuadratic p.1 (p.2 0) (p.2 1 - p.2 2) +
      2 * restartRadialRootDifference p * (p.2 1 - p.2 2) *
        (restartShearFactor p.1 * restartShearCoupling p.1 * p.2 0 +
          (restartShearCoupling p.1 ^ 2 + restartWallFactor p.1 ^ 2) * (p.2 1 - p.2 2)) +
      2 * Real.sqrt 3 * (p.2 1 + p.2 2) * restartRotationDefect p.1 (p.2 0) (p.2 1 - p.2 2) := by
  unfold restartRadialDrift restartRadialDriftCoefficients
  rw [deriv_restartGramCoefficients hn]
  dsimp [quadraticFromCoefficients, restartGramCoefficients, restartRootCoefficients,
    restartRotationCoefficients, restartQuadraticStrongDerivative, restartQuadratic, restartRotationDefect]
  ring

/-- The coefficient expression is the actual radial quadratic drift on the negative constraint branch. -/
theorem hasDerivAt_restartQuadratic_drift {x : ℝ → NormalizedState} {t : ℝ}
    (hx : HasDerivAt x (normalizedField (x t)) t) (hc : stateConstraint (x t) = 1)
    (hp : x t 0 < 0) (hn : x t 2 ^ 2 < 1) :
    HasDerivAt (fun r => restartQuadratic (x r 2) (x r 1) (x r 3 - x r 4))
      (restartRadialDrift (x t 2, restartCenterProjection (x t))) t := by
  apply (hasDerivAt_restartQuadratic_normalized hx hc hn).congr_deriv
  rw [restartRadialDrift_formula hn]
  have hroot := restart_negative_branch_root hc hp
  change -x t 0 = Real.sqrt (restartSectionRadicand (x t 2) (restartCenterProjection (x t))) at hroot
  dsimp only [restartRadialRootDifference]
  rw [← hroot]
  rfl

theorem contDiffAt_restartRadialDrift {p : RestartRadialState}
    (hn : p.1 ^ 2 < 1) (hr : 0 < restartSectionRadicand p.1 p.2) :
    ContDiffAt ℝ 3 restartRadialDrift p := by
  have HM := contDiffAt_restartRadialDriftCoefficients hn hr
  have hm (i : Fin 3) := contDiffAt_pi.mp HM i
  unfold restartRadialDrift quadraticFromCoefficients
  fun_prop

theorem fderiv_restartRadialDrift_apply {p : RestartRadialState}
    (hn : p.1 ^ 2 < 1) (hr : 0 < restartSectionRadicand p.1 p.2) (w : RestartRadialState) :
    fderiv ℝ restartRadialDrift p w =
      quadraticFromCoefficients (fderiv ℝ restartRadialDriftCoefficients p w) (p.2 0) (p.2 1 - p.2 2) +
      (2 * restartRadialDriftCoefficients p 0 * p.2 0 +
        restartRadialDriftCoefficients p 1 * (p.2 1 - p.2 2)) * w.2 0 +
      (restartRadialDriftCoefficients p 1 * p.2 0 +
        2 * restartRadialDriftCoefficients p 2 * (p.2 1 - p.2 2)) * (w.2 1 - w.2 2) := by
  have HM := (contDiffAt_restartRadialDriftCoefficients hn hr).differentiableAt (by norm_num)
  have hm (i : Fin 3) := hasFDerivAt_pi'.mp HM.hasFDerivAt i
  have hs := (hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 3) p.2).comp p (hasFDerivAt_snd (𝕜 := ℝ))
  have hv := ((hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 3) p.2).sub
    (hasFDerivAt_apply (𝕜 := ℝ) (2 : Fin 3) p.2)).comp p (hasFDerivAt_snd (𝕜 := ℝ))
  have H := (((hm 0).mul (hs.pow 2)).add (((hm 1).mul hs).mul hv)).add ((hm 2).mul (hv.pow 2))
  change HasFDerivAt restartRadialDrift _ p at H
  rw [H.fderiv]
  simp [quadraticFromCoefficients]
  ring

theorem abs_fderiv_restartRadialDrift_apply_le {p : RestartRadialState}
    (hn : p.1 ^ 2 < 1) (hr : 0 < restartSectionRadicand p.1 p.2) (w : RestartRadialState) :
    |fderiv ℝ restartRadialDrift p w| ≤
      12 * ‖fderiv ℝ restartRadialDriftCoefficients p w‖ * ‖p.2‖ ^ 2 +
        24 * ‖restartRadialDriftCoefficients p‖ * ‖p.2‖ * ‖w.2‖ := by
  rw [fderiv_restartRadialDrift_apply hn hr]
  have hb (Z : RestartCenterState) : |Z 1 - Z 2| ≤ 2 * ‖Z‖ := by
    have H := abs_sub (Z 1) (Z 2)
    have H1 : |Z 1| ≤ ‖Z‖ := norm_le_pi_norm Z 1
    have H2 : |Z 2| ≤ ‖Z‖ := norm_le_pi_norm Z 2
    linarith only [H, H1, H2]
  exact abs_quadratic_tangent_le _ _ (norm_nonneg _) (norm_nonneg _)
    (norm_le_pi_norm p.2 0) (hb _) (norm_le_pi_norm w.2 0) (hb _)

end BianchiIX
