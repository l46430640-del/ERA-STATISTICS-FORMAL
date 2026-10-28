import BianchiIX.Algebra.AxisCycle
import BianchiIX.Algebra.ExitTailBounds

noncomputable section

namespace BianchiIX

/-- A direct Young inequality controls the cyclic denominator on the whole terminal tail. -/
theorem exitCycleDenom_lower {α B R u v w : ℝ} (hα : 0 < α ∧ α ≤ 1)
    (hB : B ≤ α / 10000) (hR : |R - (2 + 2 * α)| ≤ B)
    (hw : |u| + |w| ≤ B) (hv : 0 ≤ v ∧ v ≤ 1) :
    39 / 10 * α ^ 2 + 2 / 5 * v ^ 2 < axisCycleDenom (1 - exitTailGap R v) u v w := by
  have hα0 : 0 < α := hα.1
  have hB0 : 0 ≤ B := (add_nonneg (abs_nonneg _) (abs_nonneg _)).trans hw
  have hRc := abs_le.mp hR
  have hRlo : 7 / 4 ≤ R := by linarith only [hRc.1, hB, hα.1]
  have hRhi : R ≤ 17 / 4 := by linarith only [hRc.2, hB, hα.2]
  have hR0 : 0 < R := by linarith only [hRlo]
  have hvR : v ^ 2 ≤ R ^ 2 := by nlinarith only [hRlo, hv.1, hv.2]
  have ht := exitTailGap_compact hRlo hv
  have hp : 0 < R + exitTailGap R v := by linarith only [hRlo, ht.1]
  have hp9 : R + exitTailGap R v ≤ 9 := by linarith only [hRhi, ht.2]
  have Hfrac : 4 / 9 * v ^ 2 ≤ 4 * v ^ 2 / (R + exitTailGap R v) := by
    apply (le_div_iff₀ hp).mpr
    nlinarith only [mul_le_mul_of_nonneg_right hp9 (sq_nonneg v)]
  have hρ : 199 / 100 * α ≤ R - 2 := by linarith only [hRc.1, hB, hα.1]
  have hρsq : (199 / 100 * α) ^ 2 ≤ (R - 2) ^ 2 :=
    (sq_le_sq₀ (by positivity) (by linarith only [hρ, hα.1])).mpr hρ
  have hBsq : B ^ 2 ≤ (α / 10000) ^ 2 := (sq_le_sq₀ hB0 (by positivity)).mpr hB
  have hsum : u + w ≤ B := (add_le_add (le_abs_self u) (le_abs_self w)).trans hw
  have hcross := mul_le_mul_of_nonneg_left hsum (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hv.1)
  have hYoung : 2 * v * B ≤ v ^ 2 / 100 + 100 * B ^ 2 := by nlinarith only [sq_nonneg (v / 10 - 10 * B)]
  rw [exitCycle_denom_split hR0 hvR]
  nlinarith only [Hfrac, hρsq, hBsq, hcross, hYoung, sq_nonneg (u - w), sq_pos_of_pos hα.1, sq_nonneg v]

theorem exitCycle_newWall_bound {α B H w : ℝ} (hα : 0 < α) (hB : 0 ≤ B)
    (hH : 39 / 10 * α ^ 2 < H) (hw : |w| ≤ B) :
    |4 * w / H| ≤ 2 * B / α ^ 2 := by
  have hH0 : 0 < H := lt_trans (by positivity) hH
  rw [abs_div, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4), abs_of_pos hH0]
  apply (div_le_div_iff₀ hH0 (sq_pos_of_pos hα)).mpr
  have HH : 2 * α ^ 2 ≤ H := by nlinarith only [hH, sq_nonneg α]
  nlinarith only [mul_le_mul_of_nonneg_right hw (sq_nonneg α), mul_le_mul_of_nonneg_left HH hB]

theorem exitCycle_newWall_small {α B H w : ℝ} (hα : 0 < α) (hB : 0 ≤ B)
    (hsmall : B ≤ α ^ 2 / 10000) (hH : 39 / 10 * α ^ 2 < H) (hw : |w| ≤ B) :
    |4 * w / H| ≤ 1 / 5000 := by
  apply (exitCycle_newWall_bound hα hB hH hw).trans
  apply (div_le_iff₀ (sq_pos_of_pos hα)).mpr
  linarith only [hsmall]

/-- At the auxiliary height, the full cyclic denominator is within one percent of its quadratic scale. -/
theorem exitCycleDenom_terminal_bounds {α B R u v w : ℝ} (hα : 0 < α ∧ α ≤ 1)
    (hB : B ≤ α / 10000) (hR : |R - (2 + 2 * α)| ≤ B)
    (hw : |u| + |w| ≤ B) (hv : 0 ≤ v ∧ v ≤ α / 100) :
    399 / 100 * α ^ 2 < axisCycleDenom (1 - exitTailGap R v) u v w ∧
      axisCycleDenom (1 - exitTailGap R v) u v w < 401 / 100 * α ^ 2 := by
  have hα0 : 0 < α := hα.1
  have hB0 : 0 ≤ B := (add_nonneg (abs_nonneg _) (abs_nonneg _)).trans hw
  have hRc := abs_le.mp hR
  have hRlo : 7 / 4 ≤ R := by linarith only [hRc.1, hB, hα.1]
  have hR0 : 0 < R := by linarith only [hRlo]
  have hv1 : v ≤ 1 := by linarith only [hv.2, hα.2]
  have ht := exitTailGap_compact hRlo ⟨hv.1, hv1⟩
  have hvR : v ^ 2 ≤ R ^ 2 := by nlinarith only [hRlo, hv.1, hv1]
  have hp : 0 < R + exitTailGap R v := by linarith only [hRlo, ht.1]
  have hp3 : 3 ≤ R + exitTailGap R v := by linarith only [hRc.1, hB, hα.1, ht.1]
  have Hfrac : 4 * v ^ 2 / (R + exitTailGap R v) ≤ 4 / 3 * v ^ 2 := by
    apply (div_le_iff₀ hp).mpr
    nlinarith only [mul_le_mul_of_nonneg_right hp3 (sq_nonneg v)]
  have Hfrac0 : 0 ≤ 4 * v ^ 2 / (R + exitTailGap R v) := by positivity
  have hρlo : 19999 / 10000 * α ≤ R - 2 := by linarith only [hRc.1, hB]
  have hρhi : R - 2 ≤ 20001 / 10000 * α := by linarith only [hRc.2, hB]
  have hρ0 : 0 ≤ R - 2 := by linarith only [hρlo, hα.1]
  have hρsqlo := (sq_le_sq₀ (by positivity) hρ0).mpr hρlo
  have hρsqhi := (sq_le_sq₀ hρ0 (by positivity)).mpr hρhi
  have hvsq := (sq_le_sq₀ hv.1 (by positivity)).mpr hv.2
  have herr := axisCycleDenom_wall_error (1 - exitTailGap R v) u v w
  rw [abs_of_nonneg hv.1] at herr
  have HE : (|u| + |w|) ^ 2 + 2 * v * (|u| + |w|) ≤
      (α / 10000) ^ 2 + 2 * (α / 100) * (α / 10000) := by
    gcongr <;> linarith only [hw, hB, hv.2]
  have Hb := abs_le.mp (herr.trans HE)
  have Hboundary := exitCycle_boundary_denom hR0 hvR
  constructor <;> nlinarith only [Hb.1, Hb.2, Hboundary, Hfrac0, Hfrac, hρsqlo, hρsqhi, hvsq, sq_pos_of_pos hα.1]

end BianchiIX
