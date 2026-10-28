import BianchiIX.Dynamics.StableClockFlow
import BianchiIX.Analysis.SignedRowGrowth

noncomputable section

namespace BianchiIX

def stableClockJacobian (c : ℝ) (y : StableState) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => stableBoundaryJacobian y i j / (c + 1)

theorem stableClockField_fderiv_matrix (c : ℝ) (y v : StableState) :
    fderiv ℝ (stableClockField c) y v = (stableClockJacobian c y).mulVec v := by
  rw [stableClockField_fderiv]
  ext i
  simp [stableClockJacobian, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  ring

theorem stableClockJacobian_center_bounds {c : ℝ} {y : StableState}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 10) :
    |stableClockJacobian c y 0 0| ≤ (|y 1| + |y 2|) ^ 2 / (c + 1) ∧
      |stableClockJacobian c y 0 1| ≤ 2 * (|y 1| + |y 2|) ∧
      |stableClockJacobian c y 0 2| ≤ 2 * (|y 1| + |y 2|) := by
  obtain ⟨hK, _, hm0, hmK, hm1, hm1K⟩ := stable_boundary_band hc hm
  have hK0 : 0 < c + 1 := by linarith
  have hU := mul_le_mul_of_nonneg_right hmK (abs_nonneg (y 1))
  have hU1 := mul_le_mul_of_nonneg_right hm1K (abs_nonneg (y 1))
  have hW := mul_le_mul_of_nonneg_right hm1K (abs_nonneg (y 2))
  have hW1 := mul_le_mul_of_nonneg_right (by linarith : (2 : ℝ) ≤ 2 * (c + 1)) (abs_nonneg (y 2))
  constructor
  · change |(y 1 ^ 2 - y 1 * y 2) / (c + 1)| ≤ _
    rw [abs_div, abs_of_pos hK0]
    apply div_le_div_of_nonneg_right _ hK0.le
    have H := abs_sub (y 1 ^ 2) (y 1 * y 2)
    rw [abs_of_nonneg (sq_nonneg (y 1)), abs_mul] at H
    nlinarith [sq_abs (y 1), sq_nonneg (|y 2|), mul_nonneg (abs_nonneg (y 1)) (abs_nonneg (y 2))]
  constructor
  · change |(2 * y 0 * y 1 - (y 0 + 1) * y 2) / (c + 1)| ≤ _
    rw [abs_div, abs_of_pos hK0]
    apply (div_le_iff₀ hK0).mpr
    have H := abs_sub (2 * y 0 * y 1) ((y 0 + 1) * y 2)
    simp only [abs_mul, abs_of_nonneg hm0, abs_of_nonneg hm1,
      abs_of_pos (by norm_num : (0 : ℝ) < 2)] at H
    nlinarith only [H, hU, hW]
  · change |(-(y 0 + 1) * y 1 + 2 * y 2) / (c + 1)| ≤ _
    rw [abs_div, abs_of_pos hK0]
    apply (div_le_iff₀ hK0).mpr
    have H := abs_add_le (-(y 0 + 1) * y 1) (2 * y 2)
    simp only [abs_mul, abs_neg, abs_of_nonneg hm1, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at H
    nlinarith only [H, hU1, hW1]

theorem stableClockJacobian_stable_rows {c : ℝ} {y : StableState}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 10)
    (hu : |y 1| ≤ 1 / 100) (hw : |y 2| ≤ 1 / 100) :
    stableClockJacobian c y 1 1 + |stableClockJacobian c y 1 2| ≤ -(c + 1) / 8 ∧
      stableClockJacobian c y 2 2 + |stableClockJacobian c y 2 1| ≤ -(1 / 2) := by
  obtain ⟨hK, hml, hm0, _, _, _⟩ := stable_boundary_band hc hm
  have hK0 : 0 < c + 1 := by linarith
  have hu2 : y 1 ^ 2 ≤ (1 / 100 : ℝ) ^ 2 := sq_le_sq.mpr (by norm_num; exact hu)
  have hw2 : y 2 ^ 2 ≤ (1 / 100 : ℝ) ^ 2 := sq_le_sq.mpr (by norm_num; exact hw)
  have huw : |y 1 * y 2| ≤ (1 / 100 : ℝ) ^ 2 := by
    rw [abs_mul, pow_two]
    exact mul_le_mul hu hw (abs_nonneg _) (by norm_num)
  have hm2 := (sq_le_sq₀ (by positivity : 0 ≤ (5 / 8 : ℝ) * (c + 1)) hm0).mpr hml
  constructor
  · change (1 - y 0 ^ 2 - y 2 ^ 2 + 3 * y 1 ^ 2) / 2 / (c + 1) +
      |(-y 1 * y 2) / (c + 1)| ≤ _
    rw [abs_div, abs_of_pos hK0, neg_mul, abs_neg, ← add_div]
    apply (div_le_iff₀ hK0).mpr
    nlinarith [sq_nonneg (y 2), sq_nonneg (c + 1 - 3)]
  · change -(y 0 + 1 + 2 * y 1 * y 2 - y 1 ^ 2) / (c + 1) +
      |((2 * y 1 - y 2) * y 2) / (c + 1)| ≤ _
    rw [abs_div, abs_of_pos hK0, ← add_div]
    apply (div_le_iff₀ hK0).mpr
    have H : |(2 * y 1 - y 2) * y 2| ≤ 2 * |y 1 * y 2| + y 2 ^ 2 := by
      have he : (2 * y 1 - y 2) * y 2 = 2 * (y 1 * y 2) - y 2 ^ 2 := by ring
      rw [he]
      have H' := abs_sub (2 * (y 1 * y 2)) (y 2 ^ 2)
      rw [abs_of_nonneg (sq_nonneg (y 2)), abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at H'
      exact H'
    nlinarith [(abs_le.mp huw).1]

theorem stableClockJacobian_center_column {c : ℝ} {y : StableState}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 10) :
    |stableClockJacobian c y 1 0| ≤ |y 1| ∧ |stableClockJacobian c y 2 0| ≤ |y 2| := by
  obtain ⟨hK, _, hm0, hmK, _, _⟩ := stable_boundary_band hc hm
  have hK0 : 0 < c + 1 := by linarith
  constructor
  · change |(-y 0 * y 1) / (c + 1)| ≤ _
    rw [abs_div, abs_of_pos hK0, abs_mul, abs_neg, abs_of_nonneg hm0]
    apply (div_le_iff₀ hK0).mpr
    nlinarith [mul_le_mul_of_nonneg_right hmK (abs_nonneg (y 1))]
  · change |(-y 2) / (c + 1)| ≤ _
    rw [abs_div, abs_of_pos hK0, abs_neg]
    apply (div_le_iff₀ hK0).mpr
    nlinarith [abs_nonneg (y 2)]

theorem stableClockJacobian_signedRowSum {c : ℝ} {y : StableState}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 10)
    (hu : |y 1| ≤ 1 / 100) (hw : |y 2| ≤ 1 / 100) (i : Fin 3) :
    signedRowSum (stableClockJacobian c y) i ≤ 8 * (|y 1| + |y 2|) := by
  have hK : 0 < c + 1 := by linarith
  have hb : 0 ≤ |y 1| + |y 2| := by positivity
  have hb1 : |y 1| + |y 2| ≤ 1 := by linarith
  have hb2 : (|y 1| + |y 2|) ^ 2 / (c + 1) ≤ |y 1| + |y 2| := by
    apply (div_le_iff₀ hK).mpr
    nlinarith
  have H := stableClockJacobian_center_bounds hc hm
  have C := stableClockJacobian_center_column hc hm
  have S := stableClockJacobian_stable_rows hc hm hu hw
  have hfin : Finset.univ = ({0, 1, 2} : Finset (Fin 3)) := by decide
  fin_cases i <;> simp [signedRowSum, hfin]
  · nlinarith only [H.1.trans hb2, H.2.1, H.2.2, le_abs_self (stableClockJacobian c y 0 0), hb]
  · nlinarith only [S.1, C.1, hc, abs_nonneg (y 1), abs_nonneg (y 2)]
  · nlinarith only [S.2, C.2, abs_nonneg (y 1), abs_nonneg (y 2)]

end BianchiIX
