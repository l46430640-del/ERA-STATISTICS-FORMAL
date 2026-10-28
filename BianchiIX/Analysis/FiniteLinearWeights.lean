import BianchiIX.Analysis.FiniteCoordinateBounds

noncomputable section

namespace BianchiIX

theorem clm_norm_le_weighted_coordinates {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : (Fin n → ℝ) →L[ℝ] F)
    (v : Fin n → ℝ) (B : Fin n → ℝ) (hL : ∀ i, ‖L (Pi.single i 1)‖ ≤ B i) :
    ‖L v‖ ≤ ∑ i : Fin n, |v i| * B i := by
  have hv : (∑ i : Fin n, v i • (Pi.single i 1 : Fin n → ℝ)) = v := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  have HL : L v = ∑ i : Fin n, v i • L (Pi.single i 1) := by
    rw [← hv, map_sum]
    simp only [map_smul, hv]
  calc
    ‖L v‖ = ‖∑ i : Fin n, v i • L (Pi.single i 1)‖ := congrArg norm HL
    _ ≤ ∑ i : Fin n, ‖v i • L (Pi.single i 1)‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin n, |v i| * B i := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [norm_smul, Real.norm_eq_abs] using
        mul_le_mul_of_nonneg_left (hL i) (abs_nonneg (v i))

end BianchiIX
