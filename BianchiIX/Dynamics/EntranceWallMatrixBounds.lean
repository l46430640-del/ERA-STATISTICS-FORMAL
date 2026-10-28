import BianchiIX.Dynamics.EntranceWallLinearization
import BianchiIX.Analysis.IntegralRowGrowth

noncomputable section

namespace BianchiIX

theorem entranceWallWeightedMatrix_row_bound (k : ℝ) (y : ProjectiveState) {q : ℝ}
    (hq : 0 ≤ q) (i : Fin 2) :
    signedRowSum (q • entranceWallWeightedMatrix k y) i ≤
      (entranceWallWeightedColumn k y 0 + entranceWallWeightedColumn k y 1) * q := by
  apply (signedRowSum_le_sum_abs _ _).trans
  simp only [Fin.sum_univ_two, Matrix.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg hq]
  fin_cases i
  all_goals
    dsimp [entranceWallWeightedColumn]
    nlinarith only [mul_nonneg hq (abs_nonneg (entranceWallWeightedMatrix k y 0 0)),
      mul_nonneg hq (abs_nonneg (entranceWallWeightedMatrix k y 0 1)),
      mul_nonneg hq (abs_nonneg (entranceWallWeightedMatrix k y 1 0)),
      mul_nonneg hq (abs_nonneg (entranceWallWeightedMatrix k y 1 1))]

theorem entranceWallWeightedMatrix_forcing_bound (k : ℝ) (y : ProjectiveState) {q : ℝ}
    (hq : 0 ≤ q) (v : Fin 2 → ℝ) :
    ‖(q • entranceWallWeightedMatrix k y).mulVec v‖ ≤
      (entranceWallWeightedColumn k y 0 * |v 0| + entranceWallWeightedColumn k y 1 * |v 1|) * q := by
  have hentry (i j : Fin 2) : |entranceWallWeightedMatrix k y i j| ≤ entranceWallWeightedColumn k y j := by
    fin_cases i
    · exact le_add_of_nonneg_right (abs_nonneg _)
    · exact le_add_of_nonneg_left (abs_nonneg _)
  have hM : ‖(entranceWallWeightedMatrix k y).mulVec v‖ ≤
      entranceWallWeightedColumn k y 0 * |v 0| + entranceWallWeightedColumn k y 1 * |v 1| := by
    apply (pi_norm_le_iff_of_nonneg (add_nonneg
      (mul_nonneg (entranceWallWeightedColumn_nonneg _ _ _) (abs_nonneg _))
      (mul_nonneg (entranceWallWeightedColumn_nonneg _ _ _) (abs_nonneg _)))).mpr
    intro i
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Real.norm_eq_abs]
    exact (abs_add_le _ _).trans (by
      simp only [abs_mul]
      exact add_le_add (mul_le_mul_of_nonneg_right (hentry i 0) (abs_nonneg _))
        (mul_le_mul_of_nonneg_right (hentry i 1) (abs_nonneg _)))
  rw [Matrix.smul_mulVec, norm_smul, Real.norm_eq_abs, abs_of_nonneg hq]
  exact (mul_le_mul_of_nonneg_left hM hq).trans_eq (mul_comm _ _)

end BianchiIX
