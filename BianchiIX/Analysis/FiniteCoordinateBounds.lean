import Mathlib.Analysis.Calculus.ContDiff.Operations

noncomputable section

namespace BianchiIX

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem clm_norm_le_card_mul_basis_bound {n : ℕ} (L : (Fin n → ℝ) →L[ℝ] F)
    {C : ℝ} (hC : 0 ≤ C) (hL : ∀ i, ‖L (Pi.single i 1)‖ ≤ C) : ‖L‖ ≤ n * C := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  have hv : (∑ i : Fin n, v i • (Pi.single i 1 : Fin n → ℝ)) = v := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  have HL : L v = ∑ i : Fin n, v i • L (Pi.single i 1) := by
    rw [← hv, map_sum]
    simp only [map_smul, hv]
  calc
    ‖L v‖ = ‖∑ i : Fin n, v i • L (Pi.single i 1)‖ := congrArg norm HL
    _ ≤ ∑ i : Fin n, ‖v i • L (Pi.single i 1)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin n, ‖v‖ * C := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul]
      exact mul_le_mul (norm_le_pi_norm v i) (hL i) (norm_nonneg _) (norm_nonneg v)
    _ = (n : ℝ) * C * ‖v‖ := by simp; ring

theorem bilinear_norm_le_card_mul_basis_bound {n m : ℕ}
    (L : (Fin n → ℝ) →L[ℝ] (Fin m → ℝ) →L[ℝ] F) {C : ℝ}
    (hC : 0 ≤ C) (hL : ∀ i j, ‖L (Pi.single i 1) (Pi.single j 1)‖ ≤ C) :
    ‖L‖ ≤ (n : ℝ) * m * C := by
  have H := clm_norm_le_card_mul_basis_bound L (C := m * C) (by positivity)
    (fun i => clm_norm_le_card_mul_basis_bound (L (Pi.single i 1)) hC (hL i))
  simpa only [mul_assoc] using H

end BianchiIX
