import BianchiIX.Dynamics.RestartRadialCurves

noncomputable section

namespace BianchiIX

open Set

theorem restartReferenceRadialPhase_curve_bounds {h r ρ θ ζ L : ℝ}
    (hh : 0 ≤ h ∧ h ≤ 1 / 16) (hr : 0 < r) (hρ : ρ ∈ Icc r (2 * r))
    (hL : 0 ≤ L) (hθ : |θ| ≤ L) (hζ : 0 ≤ ζ ∧ ζ ≤ r / 9) :
    r / 8 ≤ restartReferenceRadialPhase h (restartRadialCurve θ ζ ρ) ∧
      restartReferenceRadialPhase h (restartRadialCurve θ ζ ρ) ≤ 8 * (L + 1) * r := by
  let Z := restartRadialCurve θ ζ ρ
  have hnorm := (restartRadialCurve_annulus hr hρ hL hθ hζ).1
  have hsqrt : 0 < Real.sqrt (3 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hsqrtSq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hsqrt1 : 1 ≤ Real.sqrt (3 : ℝ) := by nlinarith only [hsqrtSq, hsqrt]
  have hsqrt2 : Real.sqrt (3 : ℝ) ≤ 2 := by nlinarith only [hsqrtSq, hsqrt]
  have hv : |Z 1 - Z 2| ≤ 2 * ‖Z‖ := by
    calc
      _ ≤ |Z 1| + |Z 2| := by simpa using abs_sub_le (Z 1) 0 (Z 2)
      _ ≤ ‖Z‖ + ‖Z‖ := add_le_add (norm_le_pi_norm Z 1) (norm_le_pi_norm Z 2)
      _ = _ := by ring
  have Hupper := sqrt_restartQuadratic_le_radius hh (norm_nonneg Z) (norm_le_pi_norm Z 0) hv
  have Hlower : r / 2 ≤ Real.sqrt (restartQuadratic h (Z 0) (Z 1 - Z 2)) := by
    obtain ⟨_, _, hc, _, _, _⟩ := restart_coefficients_small hh
    have hdiff : r / 2 ≤ ρ - ζ := by linarith only [hρ.1, hζ.2, hr]
    have hcv : r / 2 ≤ restartWallFactor h * (ρ - ζ) := by
      have H := mul_le_mul_of_nonneg_right hc (by linarith only [hdiff, hr] : 0 ≤ ρ - ζ)
      nlinarith only [H, hdiff]
    have H := Real.sqrt_le_sqrt (le_add_of_nonneg_left
      (sq_nonneg (restartShearFactor h * (θ * ρ) + restartShearCoupling h * (ρ - ζ))) :
      (restartWallFactor h * (ρ - ζ)) ^ 2 ≤ restartQuadratic h (θ * ρ) (ρ - ζ))
    rw [Real.sqrt_sq (by linarith only [hcv, hr])] at H
    exact hcv.trans H
  change r / 8 ≤ Real.sqrt (restartQuadratic h (Z 0) (Z 1 - Z 2)) / Real.sqrt 3 ∧
    Real.sqrt (restartQuadratic h (Z 0) (Z 1 - Z 2)) / Real.sqrt 3 ≤ 8 * (L + 1) * r
  constructor
  · apply (le_div_iff₀ hsqrt).mpr
    have H := mul_le_mul_of_nonneg_left hsqrt2 hr.le
    linarith only [Hlower, H, hr]
  · apply (div_le_iff₀ hsqrt).mpr
    have H := mul_le_mul_of_nonneg_left hsqrt1 (show 0 ≤ 8 * (L + 1) * r by positivity)
    nlinarith only [Hupper, hnorm, H]

end BianchiIX
