import BianchiIX.Analysis.SecondDerivativeRules

noncomputable section

namespace BianchiIX

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem composition_second_derivative_bounds {f : E → F} {g : F → G} {x : E} {A B K : ℝ}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g (f x))
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hf1 : ‖fderiv ℝ f x‖ ≤ K) (hf2 : ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ K)
    (hg1 : ‖fderiv ℝ g (f x)‖ ≤ A) (hg2 : ‖fderiv ℝ (fderiv ℝ g) (f x)‖ ≤ B) :
    ‖fderiv ℝ (g ∘ f) x‖ ≤ A * K ∧
      ‖fderiv ℝ (fderiv ℝ (g ∘ f)) x‖ ≤ A * K + B * K ^ 2 := by
  have hf1' (v : E) : ‖fderiv ℝ f x v‖ ≤ K * ‖v‖ :=
    ((fderiv ℝ f x).le_opNorm v).trans (mul_le_mul_of_nonneg_right hf1 (norm_nonneg v))
  have hf2' (v w : E) : ‖fderiv ℝ (fderiv ℝ f) x v w‖ ≤ K * ‖v‖ * ‖w‖ :=
    (((fderiv ℝ (fderiv ℝ f) x) v).le_opNorm w).trans
      (mul_le_mul_of_nonneg_right (((fderiv ℝ (fderiv ℝ f) x).le_opNorm v).trans
        (mul_le_mul_of_nonneg_right hf2 (norm_nonneg v))) (norm_nonneg w))
  constructor
  · rw [fderiv_comp x (hg.differentiableAt (by norm_num)) (hf.differentiableAt (by norm_num))]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul hg1 hf1 (norm_nonneg _) hA)
  · apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro v
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro w
    rw [fderiv2_comp_apply hf hg]
    have H1 := ((fderiv ℝ g (f x)).le_opNorm (fderiv ℝ (fderiv ℝ f) x v w)).trans
      (mul_le_mul hg1 (hf2' v w) (norm_nonneg _) hA)
    let L := fderiv ℝ (fderiv ℝ g) (f x)
    have H2 := ((L (fderiv ℝ f x v)).le_opNorm (fderiv ℝ f x w)).trans
      (mul_le_mul_of_nonneg_right (L.le_opNorm _) (norm_nonneg _))
    have H3 := mul_le_mul (mul_le_mul hg2 (hf1' v) (norm_nonneg _) hB)
      (hf1' w) (norm_nonneg _) (by positivity : 0 ≤ B * (K * ‖v‖))
    have Hsum := norm_add_le (fderiv ℝ g (f x) (fderiv ℝ (fderiv ℝ f) x v w))
      (L (fderiv ℝ f x v) (fderiv ℝ f x w))
    dsimp only [L] at H2 Hsum
    nlinarith only [H1, H2, H3, Hsum]

end BianchiIX
