import BianchiIX.Dynamics.ExitSinglePhaseDifferential

noncomputable section

namespace BianchiIX

def exitSingleBoundarySlope (R v : ℝ) : ℝ :=
  -(1 + (R ^ 2 - 4) / exitSingleBase R v) / (2 * R)

theorem exitSingleBase_boundary_lower {R v : ℝ} (hR : 2 < R) (hv : v ^ 2 ≤ R ^ 2) :
    (R - 2) ^ 2 ≤ exitSingleBase R v := by
  have hR0 : 0 < R := by linarith only [hR]
  have H := exitCycle_denom_split hR0 hv (0 : ℝ) 0
  rw [← exitSingleBase_eq] at H
  simp only [sub_self, zero_pow (by norm_num : 2 ≠ 0), add_zero, mul_zero, sub_zero] at H
  rw [H]
  exact le_add_of_nonneg_right (div_nonneg (by positivity)
    (add_nonneg hR0.le (Real.sqrt_nonneg _)))

theorem exitSingleBoundarySlope_zero {R : ℝ} (hR : 2 < R) :
    exitSingleBoundarySlope R 0 = -1 / (R - 2) := by
  have hR0 : 0 < R := by linarith only [hR]
  have hR2 : R - 2 ≠ 0 := (sub_pos.mpr hR).ne'
  simp only [exitSingleBoundarySlope, exitSingleBase, exitTailGap, zero_pow (by norm_num : 2 ≠ 0),
    sub_zero, Real.sqrt_sq hR0.le, add_zero]
  have h2R : 2 - R ≠ 0 := by linarith only [hR]
  field_simp
  ring

/-- The finite-height single-wall phase has the same ordinary coefficient in both wall columns. -/
theorem exitSinglePhase_boundary_differential {R v : ℝ} (hR : 2 < R) (hv : v ^ 2 < R ^ 2) :
    ContDiffAt ℝ 2 (fun Z : ExitTailState => exitSinglePhase (Z 0) (Z 1) v (Z 2)) ![R, 0, 0] ∧
      ∀ d : ExitTailState,
        fderiv ℝ (fun Z : ExitTailState => exitSinglePhase (Z 0) (Z 1) v (Z 2)) ![R, 0, 0] d =
          d 0 / 2 + v * exitSingleBoundarySlope R v * (d 1 + d 2) := by
  have hR0 : 0 < R := by linarith only [hR]
  have hH : 0 < exitSingleBase R v :=
    (sq_pos_of_pos (sub_pos.mpr hR)).trans_le (exitSingleBase_boundary_lower hR hv.le)
  have hS : 0 < R ^ 2 + exitSingleError R 0 v 0 := by
    simpa [exitSingleError, exitSingleDefect] using sq_pos_of_pos hR0
  have H := exitSinglePhase_differential (Y := ![R, 0, 0]) hv hH.ne' hS
  refine ⟨H.1, ?_⟩
  intro d
  rw [H.2 d]
  change ((2 * R + exitSingleErrorRadial R 0 v 0) * d 0 +
    exitSingleErrorWallFactor R 0 v 0 * ((2 * (0 - 0) - 2 * v) * d 1 +
      (-2 * (0 - 0) - 2 * v) * d 2)) / (4 * Real.sqrt (R ^ 2 + exitSingleError R 0 v 0)) = _
  simp only [exitSingleErrorRadial, exitSingleErrorWallFactor, exitSingleError, exitSingleDefect,
    sub_self, zero_pow (by norm_num : 2 ≠ 0), add_zero, mul_zero, zero_mul, Real.sqrt_sq hR0.le]
  dsimp only [exitSingleBoundarySlope]
  field_simp
  ring

end BianchiIX
