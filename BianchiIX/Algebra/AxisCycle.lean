import BianchiIX.Algebra.Coordinates
import BianchiIX.Algebra.ExitTail

noncomputable section

namespace BianchiIX

def axisCycleDenom (m u v w : ℝ) : ℝ := (m + 1) ^ 2 + curvature u v w

theorem axisCycleDenom_projective (m u v w : ℝ) :
    axisCycleDenom m u v w = projectiveDenom m u v w + 2 * m - 2 := by
  unfold axisCycleDenom projectiveDenom
  ring

theorem axisCycleDenom_wall_split (m u v w : ℝ) :
    axisCycleDenom m u v w = (m + 1) ^ 2 + v ^ 2 + (u - w) ^ 2 - 2 * v * (u + w) := by
  unfold axisCycleDenom curvature
  ring

/-- The boundary part of the cyclic chart denominator retains both radial and active-wall separation. -/
theorem exitCycle_boundary_denom {R v : ℝ} (hR : 0 < R) (hv : v ^ 2 ≤ R ^ 2) :
    (2 - exitTailGap R v) ^ 2 + v ^ 2 = (R - 2) ^ 2 + 4 * v ^ 2 / (R + exitTailGap R v) := by
  have ht0 : 0 ≤ exitTailGap R v := Real.sqrt_nonneg _
  have hp : R + exitTailGap R v ≠ 0 := (add_pos_of_pos_of_nonneg hR ht0).ne'
  have ht := exitTailGap_sq hv
  field_simp
  nlinarith only [ht, congrArg (fun x => R * x) ht, congrArg (fun x => exitTailGap R v * x) ht]

theorem exitCycle_denom_split {R v : ℝ} (hR : 0 < R) (hv : v ^ 2 ≤ R ^ 2) (u w : ℝ) :
    axisCycleDenom (1 - exitTailGap R v) u v w =
      (R - 2) ^ 2 + 4 * v ^ 2 / (R + exitTailGap R v) + (u - w) ^ 2 - 2 * v * (u + w) := by
  rw [axisCycleDenom_wall_split]
  have H := exitCycle_boundary_denom hR hv
  nlinarith only [H]

theorem axisCycleDenom_wall_error (m u v w : ℝ) :
    |axisCycleDenom m u v w - ((m + 1) ^ 2 + v ^ 2)| ≤
      (|u| + |w|) ^ 2 + 2 * |v| * (|u| + |w|) := by
  rw [axisCycleDenom_wall_split]
  have H := abs_sub ((u - w) ^ 2) (2 * v * (u + w))
  simp only [abs_of_nonneg (sq_nonneg (u - w)), abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at H
  have HS : (u - w) ^ 2 ≤ (|u| + |w|) ^ 2 := by
    have HD := abs_sub u w
    nlinarith only [sq_abs (u - w), (sq_le_sq₀ (abs_nonneg _) (add_nonneg (abs_nonneg _) (abs_nonneg _))).mpr HD]
  have HM := mul_le_mul_of_nonneg_left (abs_add_le u w) (by positivity : 0 ≤ 2 * |v|)
  rw [show (m + 1) ^ 2 + v ^ 2 + (u - w) ^ 2 - 2 * v * (u + w) - ((m + 1) ^ 2 + v ^ 2) =
    (u - w) ^ 2 - 2 * v * (u + w) by ring]
  exact H.trans (add_le_add HS HM)

end BianchiIX
