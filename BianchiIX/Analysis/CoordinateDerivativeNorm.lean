import Mathlib.Analysis.Calculus.ContDiff.Operations

noncomputable section

namespace BianchiIX

theorem fderiv_norm_le_of_coordinate_bounds {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} {f : E → Fin n → ℝ} {x : E} {C : ℝ} (hC : 0 ≤ C)
    (hf : DifferentiableAt ℝ f x) (hbound : ∀ i, ‖fderiv ℝ (fun y => f y i) x‖ ≤ C) :
    ‖fderiv ℝ f x‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro v
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hC (norm_nonneg v))).mpr
  intro i
  have heq := congrArg (fun L : E →L[ℝ] ℝ => L v) (fderiv_apply hf i)
  change fderiv ℝ (fun y => f y i) x v = (fderiv ℝ f x v) i at heq
  rw [← heq]
  exact ((fderiv ℝ (fun y => f y i) x).le_opNorm v).trans
    (mul_le_mul_of_nonneg_right (hbound i) (norm_nonneg v))

end BianchiIX
