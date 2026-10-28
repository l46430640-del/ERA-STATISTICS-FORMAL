import BianchiIX.Analysis.SecondDerivativeRules

noncomputable section

namespace BianchiIX

open Filter
open scoped Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem product_second_derivative_bounds {f g : E → ℝ} {x : E} {A B : ℝ}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hf0 : |f x| ≤ A) (hf1 : ‖fderiv ℝ f x‖ ≤ A) (hf2 : ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ A)
    (hg0 : |g x| ≤ B) (hg1 : ‖fderiv ℝ g x‖ ≤ B) (hg2 : ‖fderiv ℝ (fderiv ℝ g) x‖ ≤ B) :
    |f x * g x| ≤ A * B ∧ ‖fderiv ℝ (fun y => f y * g y) x‖ ≤ 2 * A * B ∧
      ‖fderiv ℝ (fderiv ℝ (fun y => f y * g y)) x‖ ≤ 4 * A * B := by
  have hf1' (v : E) : |fderiv ℝ f x v| ≤ A * ‖v‖ :=
    ((fderiv ℝ f x).le_opNorm v).trans (mul_le_mul_of_nonneg_right hf1 (norm_nonneg v))
  have hg1' (v : E) : |fderiv ℝ g x v| ≤ B * ‖v‖ :=
    ((fderiv ℝ g x).le_opNorm v).trans (mul_le_mul_of_nonneg_right hg1 (norm_nonneg v))
  have hf2' (v w : E) : |fderiv ℝ (fderiv ℝ f) x v w| ≤ A * ‖v‖ * ‖w‖ :=
    (((fderiv ℝ (fderiv ℝ f) x) v).le_opNorm w).trans
      (mul_le_mul_of_nonneg_right (((fderiv ℝ (fderiv ℝ f) x).le_opNorm v).trans
        (mul_le_mul_of_nonneg_right hf2 (norm_nonneg v))) (norm_nonneg w))
  have hg2' (v w : E) : |fderiv ℝ (fderiv ℝ g) x v w| ≤ B * ‖v‖ * ‖w‖ :=
    (((fderiv ℝ (fderiv ℝ g) x) v).le_opNorm w).trans
      (mul_le_mul_of_nonneg_right (((fderiv ℝ (fderiv ℝ g) x).le_opNorm v).trans
        (mul_le_mul_of_nonneg_right hg2 (norm_nonneg v))) (norm_nonneg w))
  refine ⟨by rw [abs_mul]; exact mul_le_mul hf0 hg0 (abs_nonneg _) hA, ?_, ?_⟩
  · apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro v
    rw [fderiv_fun_mul (hf.differentiableAt (by norm_num)) (hg.differentiableAt (by norm_num))]
    change |f x * fderiv ℝ g x v + g x * fderiv ℝ f x v| ≤ _
    have H := abs_add_le (f x * fderiv ℝ g x v) (g x * fderiv ℝ f x v)
    simp only [abs_mul] at H
    nlinarith only [H, mul_le_mul hf0 (hg1' v) (abs_nonneg _) hA,
      mul_le_mul hg0 (hf1' v) (abs_nonneg _) hB]
  · apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro v
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro w
    rw [Real.norm_eq_abs, fderiv2_mul_apply hf hg]
    have htri (a b c d : ℝ) : |a + b + c + d| ≤ |a| + |b| + |c| + |d| := by
      linarith only [abs_add_le a b, abs_add_le (a + b) c, abs_add_le (a + b + c) d]
    have H := htri (f x * fderiv ℝ (fderiv ℝ g) x v w)
      (fderiv ℝ f x v * fderiv ℝ g x w) (fderiv ℝ f x w * fderiv ℝ g x v)
      (fderiv ℝ (fderiv ℝ f) x v w * g x)
    simp only [abs_mul] at H
    nlinarith only [H, mul_le_mul hf0 (hg2' v w) (abs_nonneg _) hA,
      mul_le_mul (hf1' v) (hg1' w) (abs_nonneg _) (mul_nonneg hA (norm_nonneg v)),
      mul_le_mul (hf1' w) (hg1' v) (abs_nonneg _) (mul_nonneg hA (norm_nonneg w)),
      mul_le_mul (hf2' v w) hg0 (abs_nonneg _) (mul_nonneg (mul_nonneg hA (norm_nonneg v)) (norm_nonneg w))]

theorem clm_precomp_second_derivative_bounds {g : F → ℝ} {x : E} {B : ℝ}
    (L : E →L[ℝ] F) (hL : ‖L‖ ≤ 1) (hB : 0 ≤ B) (hg : ContDiffAt ℝ 2 g (L x))
    (hg1 : ‖fderiv ℝ g (L x)‖ ≤ B) (hg2 : ‖fderiv ℝ (fderiv ℝ g) (L x)‖ ≤ B) :
    ‖fderiv ℝ (g ∘ L) x‖ ≤ B ∧ ‖fderiv ℝ (fderiv ℝ (g ∘ L)) x‖ ≤ B := by
  have hLv (v : E) : ‖L v‖ ≤ ‖v‖ :=
    (L.le_opNorm v).trans (mul_le_of_le_one_left (norm_nonneg v) hL)
  have hLd : fderiv ℝ (L : E → F) = fun _ => L := funext (fun _ => L.fderiv)
  constructor
  · rw [fderiv_comp x (hg.differentiableAt (by norm_num)) L.differentiableAt]
    apply ContinuousLinearMap.opNorm_le_bound _ hB
    intro v
    simp only [ContinuousLinearMap.comp_apply, hLd]
    exact ((fderiv ℝ g (L x)).le_opNorm (L v)).trans (mul_le_mul hg1 (hLv v) (norm_nonneg _) hB)
  · apply ContinuousLinearMap.opNorm_le_bound _ hB
    intro v
    apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hB (norm_nonneg v))
    intro w
    have H := fderiv2_comp_apply L.contDiff.contDiffAt hg v w
    simp only [hLd, fderiv_const_apply, zero_apply, map_zero, zero_add] at H
    rw [H]
    have H0 := (((fderiv ℝ (fderiv ℝ g) (L x)) (L v)).le_opNorm (L w)).trans
      (mul_le_mul_of_nonneg_right ((fderiv ℝ (fderiv ℝ g) (L x)).le_opNorm (L v)) (norm_nonneg (L w)))
    exact H0.trans (mul_le_mul (mul_le_mul hg2 (hLv v) (norm_nonneg _) hB) (hLv w)
      (norm_nonneg _) (mul_nonneg hB (norm_nonneg v)))

theorem fderiv2_finset_sum_apply {ι : Type*} (s : Finset ι) {f : ι → E → F} {x : E}
    (hf : ∀ i ∈ s, ContDiffAt ℝ 2 (f i) x) (v w : E) :
    fderiv ℝ (fderiv ℝ (fun y => ∑ i ∈ s, f i y)) x v w =
      ∑ i ∈ s, fderiv ℝ (fderiv ℝ (f i)) x v w := by
  have heq : fderiv ℝ (fun y => ∑ i ∈ s, f i y) =ᶠ[𝓝 x]
      (fun y => ∑ i ∈ s, fderiv ℝ (f i) y) := by
    have hnear : ∀ᶠ y in 𝓝 x, ∀ i ∈ s, ContDiffAt ℝ 2 (f i) y :=
      (s.eventually_all).mpr (fun i hi => (hf i hi).eventually (by norm_num))
    filter_upwards [hnear] with y hy
    exact fderiv_fun_sum (fun i hi => (hy i hi).differentiableAt (by norm_num))
  have H := HasFDerivAt.fun_sum (u := s) (fun i hi =>
    ((hf i hi).fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiableAt (by norm_num) |>.hasFDerivAt)
  have H' := congrArg (fun L : E →L[ℝ] (E →L[ℝ] F) => L v w) (H.congr_of_eventuallyEq heq).fderiv
  simpa only [sum_apply] using H'

end BianchiIX
