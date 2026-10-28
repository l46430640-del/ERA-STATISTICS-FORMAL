import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.Ring

noncomputable section

namespace BianchiIX

open Set

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- An affine bound on the derivative along a ray retains the factor one half in the quadratic remainder. -/
theorem norm_le_quadratic_of_radial_fderiv {f : E → F} {x : E} {A B : ℝ}
    (hzero : f 0 = 0)
    (hf : ∀ θ ∈ Icc (0 : ℝ) 1, DifferentiableAt ℝ f (θ • x))
    (hbound : ∀ θ ∈ Icc (0 : ℝ) 1, ‖fderiv ℝ f (θ • x)‖ ≤ A * θ * ‖x‖ + B) :
    ‖f x‖ ≤ A / 2 * ‖x‖ ^ 2 + B * ‖x‖ := by
  let g := fun θ : ℝ => f (θ • x)
  let R := fun θ : ℝ => A / 2 * θ ^ 2 * ‖x‖ ^ 2 + B * θ * ‖x‖
  have hg (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) 1) :
      HasDerivAt g (fderiv ℝ f (θ • x) x) θ := by
    convert! (hf θ hθ).hasFDerivAt.comp_hasDerivAt θ ((hasDerivAt_id' θ).smul_const x) using 1
    simp only [one_smul]
  have hR (θ : ℝ) : HasDerivAt R ((A * θ * ‖x‖ + B) * ‖x‖) θ := by
    convert! ((((hasDerivAt_id' θ).pow 2).const_mul (A / 2)).mul_const (‖x‖ ^ 2)).add
      (((hasDerivAt_id' θ).const_mul B).mul_const ‖x‖) using 1
    ring
  have H := image_norm_le_of_norm_deriv_right_le_deriv_boundary (HasDerivAt.continuousOn hg)
    (fun θ hθ => (hg θ (Ico_subset_Icc_self hθ)).hasDerivWithinAt)
    (by simp [g, R, hzero] : ‖g 0‖ ≤ R 0) hR
    (fun θ hθ => ((fderiv ℝ f (θ • x)).le_opNorm x).trans
      (mul_le_mul_of_nonneg_right (hbound θ (Ico_subset_Icc_self hθ)) (norm_nonneg x)))
    (show (1 : ℝ) ∈ Icc 0 1 from ⟨zero_le_one, le_rfl⟩)
  simpa only [g, R, one_smul, one_pow, mul_one] using H

end BianchiIX
