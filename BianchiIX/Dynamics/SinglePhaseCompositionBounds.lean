import BianchiIX.Dynamics.ExitActualDirections
import BianchiIX.Analysis.FiniteCoordinateBounds

noncomputable section

namespace BianchiIX

theorem clm_three_radial_composition_bound (P : ExitTailState →L[ℝ] ℝ) (d : ExitTailState) :
    |P d - 1 / 2| ≤ |P (Pi.single 0 1) - 1 / 2| * |d 0| + |d 0 - 1| / 2 +
      (|P (Pi.single 1 1)| + |P (Pi.single 2 1)|) * (|d 1| + |d 2|) := by
  let Q : ExitTailState →L[ℝ] ℝ := P - (1 / 2 : ℝ) • ContinuousLinearMap.proj 0
  have H := clm_three_coordinate_bound Q d
  have H0 : Q (Pi.single 0 1) = P (Pi.single 0 1) - 1 / 2 := by simp [Q]
  have H1 : Q (Pi.single 1 1) = P (Pi.single 1 1) := by simp [Q]
  have H2 : Q (Pi.single 2 1) = P (Pi.single 2 1) := by simp [Q]
  rw [H0, H1, H2] at H
  have Heq : P d - 1 / 2 = Q d + (d 0 - 1) / 2 := by
    simp only [Q, sub_apply, smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
    ring
  rw [Heq]
  have Hsum := abs_add_le (Q d) ((d 0 - 1) / 2)
  rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at Hsum
  nlinarith only [H, Hsum, mul_nonneg (abs_nonneg (P (Pi.single 1 1))) (abs_nonneg (d 2)),
    mul_nonneg (abs_nonneg (P (Pi.single 2 1))) (abs_nonneg (d 1))]

end BianchiIX
