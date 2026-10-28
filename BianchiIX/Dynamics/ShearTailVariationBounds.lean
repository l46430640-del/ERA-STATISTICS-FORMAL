import BianchiIX.Dynamics.ShearTailDifferential
import BianchiIX.Dynamics.ShearTailMoments

noncomputable section

namespace BianchiIX

/-- Polynomial responses retain their wall amplitudes, including on zero-wall faces. -/
theorem shearTail_polynomial_variation_bounds {z v : NormalizedState} {L : ℝ}
    (hL : 0 ≤ L) (hn : 0 ≤ z 2 ∧ 0 ≤ z 3 ∧ 0 ≤ z 4)
    (hv : |v 2| ≤ z 2 * L ∧ |v 3| ≤ z 3 * L ∧ |v 4| ≤ z 4 * L) :
    |curvature (z 2) (z 3) (z 4)| ≤ 2 * shearTailEnergy z ∧
    |shearTailCurvatureDifferential z v| ≤ 4 * shearTailEnergy z * L ∧
    |shearTailCouplingDifferential z v| ≤ 2 * shearTailEnergy z * L := by
  let M := z 2 + z 3 + z 4
  have hM : 0 ≤ M := by dsimp only [M]; positivity [hn.1, hn.2.1, hn.2.2]
  have hM2 : M ^ 2 ≤ 2 * shearTailEnergy z := by
    dsimp only [M, shearTailEnergy]
    nlinarith only [sq_nonneg (z 2), sq_nonneg (z 3 - z 4)]
  have hcoef : |z 2 - z 3 - z 4| ≤ M ∧ |z 3 - z 2 - z 4| ≤ M ∧ |z 4 - z 2 - z 3| ≤ M := by
    dsimp only [M]
    refine ⟨abs_le.mpr ⟨?_, ?_⟩, abs_le.mpr ⟨?_, ?_⟩, abs_le.mpr ⟨?_, ?_⟩⟩ <;>
      linarith only [hn.1, hn.2.1, hn.2.2]
  have HQraw : |shearTailCurvatureDifferential z v| ≤ 2 * M ^ 2 * L := by
    have H := abs_add_three ((z 2 - z 3 - z 4) * v 2) ((z 3 - z 2 - z 4) * v 3)
      ((z 4 - z 2 - z 3) * v 4)
    simp only [abs_mul] at H
    have Hn := mul_le_mul hcoef.1 hv.1 (abs_nonneg _) hM
    have Hx := mul_le_mul hcoef.2.1 hv.2.1 (abs_nonneg _) hM
    have Hy := mul_le_mul hcoef.2.2 hv.2.2 (abs_nonneg _) hM
    dsimp only [shearTailCurvatureDifferential]
    rw [abs_mul, abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
    dsimp only [M] at Hn Hx Hy ⊢
    nlinarith only [H, Hn, Hx, Hy]
  refine ⟨(curvature_abs_le_sum_sq hn.1 hn.2.1 hn.2.2).trans hM2,
    HQraw.trans (by nlinarith only [mul_le_mul_of_nonneg_right hM2 hL]), ?_⟩
  have H := abs_add_three ((z 3 - z 4) * v 2) ((z 2 - 2 * z 3) * v 3) ((2 * z 4 - z 2) * v 4)
  simp only [abs_mul] at H
  have Hn := mul_le_mul (show |z 3 - z 4| ≤ z 3 + z 4 by
    exact abs_le.mpr ⟨by linarith only [hn.2.1], by linarith only [hn.2.2]⟩)
    hv.1 (abs_nonneg _) (add_nonneg hn.2.1 hn.2.2)
  have Hx := mul_le_mul (show |z 2 - 2 * z 3| ≤ z 2 + 2 * z 3 by
    exact abs_le.mpr ⟨by linarith only [hn.1], by linarith only [hn.2.1]⟩)
    hv.2.1 (abs_nonneg _) (by positivity [hn.1, hn.2.1] : 0 ≤ z 2 + 2 * z 3)
  have Hy := mul_le_mul (show |2 * z 4 - z 2| ≤ 2 * z 4 + z 2 by
    exact abs_le.mpr ⟨by linarith only [hn.2.2], by linarith only [hn.1]⟩)
    hv.2.2 (abs_nonneg _) (by positivity [hn.1, hn.2.2] : 0 ≤ 2 * z 4 + z 2)
  dsimp only [shearTailCouplingDifferential, shearTailEnergy]
  nlinarith only [H, Hn, Hx, Hy, mul_nonneg (sq_nonneg (z 2)) hL]

/-- The two differential inequalities of (E.43) use the same energy as the time-moment estimates. -/
theorem shearTailVariationRate_bounds {z v : NormalizedState} {L : ℝ}
    (hp : z 0 ≤ -(15 / 16)) (hs : |z 1| ≤ 1 / 8)
    (hL : 0 ≤ L) (hn : 0 ≤ z 2 ∧ 0 ≤ z 3 ∧ 0 ≤ z 4)
    (hv : |v 2| ≤ z 2 * L ∧ |v 3| ≤ z 3 * L ∧ |v 4| ≤ z 4 * L) :
    |shearTailVariationRate z v 0| ≤ 2 * shearTailEnergy z * |v 1| + 4 * shearTailEnergy z * L ∧
    ∀ i : Fin 3, |shearTailVariationRate z v i.succ| ≤ 2 * |v 1| + 9 * shearTailEnergy z * L := by
  obtain ⟨HQ, HdQ, HdH⟩ := shearTail_polynomial_variation_bounds hL hn hv
  have hb : 0 ≤ shearTailEnergy z := by dsimp only [shearTailEnergy]; positivity [hn.1, hn.2.1, hn.2.2]
  have hξ : 0 < -z 0 := by linarith only [hp]
  have hi : 0 ≤ (-z 0)⁻¹ ∧ (-z 0)⁻¹ ≤ 5 / 4 := by
    refine ⟨inv_nonneg.mpr hξ.le, ?_⟩
    rw [inv_eq_one_div]
    apply (div_le_iff₀ hξ).mpr
    linarith only [hp]
  have hr : |Real.sqrt (3 : ℝ)| ≤ 7 / 4 := by
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    nlinarith only [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg (3 : ℝ)]
  have hsi : |z 1| * (-z 0)⁻¹ ≤ 1 / 4 := by
    have H := mul_le_mul hs hi.2 hi.1 (by norm_num : (0 : ℝ) ≤ 1 / 8)
    nlinarith only [H]
  have hc1 : |1 + (-z 0)⁻¹| ≤ 9 / 4 := by
    rw [abs_of_nonneg (by linarith only [hi.1] : 0 ≤ 1 + (-z 0)⁻¹)]
    linarith only [hi.2]
  have hc2 : |1 - (2 * (-z 0))⁻¹| ≤ 9 / 4 := by
    rw [mul_inv_rev]
    norm_num only [invOf_eq_inv, inv_eq_one_div]
    apply abs_le.mpr
    rw [← inv_eq_one_div] at *
    constructor <;> nlinarith only [hi.1, hi.2]
  have hs1 : |2 * z 1 * (-z 0)⁻¹| ≤ 2 := by
    rw [abs_mul, abs_mul, abs_of_pos (show (0 : ℝ) < 2 by norm_num), abs_of_nonneg hi.1]
    nlinarith only [hsi]
  have hsp : |-z 1 * (-z 0)⁻¹ + Real.sqrt 3| ≤ 2 := by
    have H := abs_add_le (-z 1 * (-z 0)⁻¹) (Real.sqrt 3)
    rw [abs_mul, abs_neg, abs_of_nonneg hi.1] at H
    linarith only [H, hsi, hr]
  have hsm : |-z 1 * (-z 0)⁻¹ - Real.sqrt 3| ≤ 2 := by
    have H := abs_sub (-z 1 * (-z 0)⁻¹) (Real.sqrt 3)
    rw [abs_mul, abs_neg, abs_of_nonneg hi.1] at H
    linarith only [H, hsi, hr]
  have Hrow (A B : ℝ) (hA : |A| ≤ 9 / 4) (hB : |B| ≤ 2) :
      |A * shearTailCurvatureDifferential z v + B * v 1| ≤ 2 * |v 1| + 9 * shearTailEnergy z * L := by
    have H := abs_add_le (A * shearTailCurvatureDifferential z v) (B * v 1)
    rw [abs_mul, abs_mul] at H
    have HA := mul_le_mul hA HdQ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 9 / 4)
    have HB := mul_le_mul_of_nonneg_right hB (abs_nonneg (v 1))
    nlinarith only [H, HA, HB]
  constructor
  · have H := abs_add_three (curvature (z 2) (z 3) (z 4) * v 1)
      (z 1 * shearTailCurvatureDifferential z v) (Real.sqrt 3 * shearTailCouplingDifferential z v)
    simp only [abs_mul] at H
    have Hq := mul_le_mul_of_nonneg_right HQ (abs_nonneg (v 1))
    have Hs := mul_le_mul hs HdQ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 / 8)
    have Hr := mul_le_mul hr HdH (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 7 / 4)
    change |curvature (z 2) (z 3) (z 4) * v 1 + z 1 * shearTailCurvatureDifferential z v +
      Real.sqrt 3 * shearTailCouplingDifferential z v| ≤ _
    nlinarith only [H, Hq, Hs, Hr]
  · intro i
    fin_cases i
    · exact Hrow _ _ hc1 hs1
    · exact Hrow _ _ hc2 hsp
    · exact Hrow _ _ hc2 hsm

def shearTailLogSize (z v : NormalizedState) : ℝ :=
  ‖fun i : Fin 3 => v (i.addNat 2) / z (i.addNat 2)‖

/-- For positive walls the relative bound is supplied by the actual logarithmic tangent. -/
theorem shearTailVariationRate_log_bounds {z v : NormalizedState}
    (hp : z 0 ≤ -(15 / 16)) (hs : |z 1| ≤ 1 / 8) (hn : positiveWalls z) :
    |shearTailVariationRate z v 0| ≤
      2 * shearTailEnergy z * |v 1| + 4 * shearTailEnergy z * shearTailLogSize z v ∧
    ∀ i : Fin 3, |shearTailVariationRate z v i.succ| ≤
      2 * |v 1| + 9 * shearTailEnergy z * shearTailLogSize z v := by
  have H (i : Fin 3) (hi : 0 < z (i.addNat 2)) :
      |v (i.addNat 2)| ≤ z (i.addNat 2) * shearTailLogSize z v := by
    have h := norm_le_pi_norm (fun j : Fin 3 => v (j.addNat 2) / z (j.addNat 2)) i
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hi] at h
    have := (div_le_iff₀ hi).mp h
    simpa only [shearTailLogSize, mul_comm] using this
  exact shearTailVariationRate_bounds hp hs (norm_nonneg _)
    ⟨hn.1.le, hn.2.1.le, hn.2.2.le⟩ ⟨H 0 hn.1, H 1 hn.2.1, H 2 hn.2.2⟩

end BianchiIX
