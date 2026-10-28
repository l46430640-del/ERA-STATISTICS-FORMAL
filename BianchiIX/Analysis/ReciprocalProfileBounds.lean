import BianchiIX.Analysis.ReciprocalCoordinates

noncomputable section

namespace BianchiIX

theorem reciprocalProfile_derivative_bounds {g : (Fin 2 → ℝ) → ℝ} {y : Fin 2 → ℝ} {B : ℝ}
    (hy : 3 / 2 ≤ y 0) (hB : 0 ≤ B)
    (hg : ContDiffAt ℝ 2 g (reciprocalParameterMap y))
    (hg0 : |g (reciprocalParameterMap y)| ≤ B)
    (hg1 : ‖fderiv ℝ g (reciprocalParameterMap y)‖ ≤ B)
    (hg2 : ‖fderiv ℝ (fderiv ℝ g) (reciprocalParameterMap y)‖ ≤ B) :
    |reciprocalParameter y * g (reciprocalParameterMap y)| ≤ B * reciprocalParameter y ∧
      ‖fderiv ℝ (fun z => reciprocalParameter z * g (reciprocalParameterMap z)) y‖ ≤
        2 * B * reciprocalParameter y ∧
      ‖fderiv ℝ (fderiv ℝ (fun z => reciprocalParameter z * g (reciprocalParameterMap z))) y‖ ≤
        7 * B * reciprocalParameter y := by
  let a := reciprocalParameter y
  let f := fun z => g (reciprocalParameterMap z)
  have ha : 0 ≤ a := (reciprocalParameter_range hy).1.le
  have hn : y 0 + 1 ≠ 0 := by linarith
  have haReg := contDiffAt_reciprocalParameter 2 hn
  have hpReg := contDiffAt_reciprocalParameterMap 2 hn
  have hfReg : ContDiffAt ℝ 2 f y := hg.comp y hpReg
  have hf1 (v : Fin 2 → ℝ) : |fderiv ℝ f y v| ≤ B * ‖v‖ := by
    have heq : fderiv ℝ f y v = fderiv ℝ g (reciprocalParameterMap y)
        (fderiv ℝ reciprocalParameterMap y v) := by
      rw [show f = g ∘ reciprocalParameterMap from rfl, fderiv_comp y
        (hg.differentiableAt (by norm_num)) (hpReg.differentiableAt (by norm_num))]
      rfl
    rw [heq]
    exact ((fderiv ℝ g (reciprocalParameterMap y)).le_opNorm _).trans
      (mul_le_mul hg1 (reciprocalParameter_derivative_bounds hy v v).2.2.1 (norm_nonneg _) hB)
  have hf2 (v w : Fin 2 → ℝ) : |fderiv ℝ (fderiv ℝ f) y v w| ≤ 3 * B * ‖v‖ * ‖w‖ := by
    rw [show f = g ∘ reciprocalParameterMap from rfl, fderiv2_comp_apply hpReg hg]
    have H1 := ((fderiv ℝ g (reciprocalParameterMap y)).le_opNorm
      (fderiv ℝ (fderiv ℝ reciprocalParameterMap) y v w)).trans
      (mul_le_mul hg1 (reciprocalParameter_derivative_bounds hy v w).2.2.2 (norm_nonneg _) hB)
    let L := fderiv ℝ (fderiv ℝ g) (reciprocalParameterMap y)
    have H2 := ((L (fderiv ℝ reciprocalParameterMap y v)).le_opNorm
      (fderiv ℝ reciprocalParameterMap y w)).trans
      (mul_le_mul_of_nonneg_right (L.le_opNorm _) (norm_nonneg _))
    have H3 := mul_le_mul
      (mul_le_mul hg2 (reciprocalParameter_derivative_bounds hy v w).2.2.1 (norm_nonneg _) hB)
      (reciprocalParameter_derivative_bounds hy w v).2.2.1 (norm_nonneg _) (by positivity : 0 ≤ B * ‖v‖)
    have Hsum := abs_add_le
      (fderiv ℝ g (reciprocalParameterMap y) (fderiv ℝ (fderiv ℝ reciprocalParameterMap) y v w))
      (L (fderiv ℝ reciprocalParameterMap y v) (fderiv ℝ reciprocalParameterMap y w))
    simp only [Real.norm_eq_abs, L] at H1 H2 Hsum
    nlinarith only [H1, H2, H3, Hsum]
  refine ⟨?_, ?_, ?_⟩
  · rw [abs_mul, abs_of_nonneg ha]
    nlinarith only [mul_le_mul_of_nonneg_left hg0 ha]
  · apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro v
    rw [fderiv_fun_mul (haReg.differentiableAt (by norm_num)) (hfReg.differentiableAt (by norm_num))]
    change |reciprocalParameter y * fderiv ℝ f y v + f y * fderiv ℝ reciprocalParameter y v| ≤ _
    have H := abs_add_le (reciprocalParameter y * fderiv ℝ f y v) (f y * fderiv ℝ reciprocalParameter y v)
    rw [abs_mul, abs_mul, abs_of_nonneg ha] at H
    have H1 := mul_le_mul_of_nonneg_left (hf1 v) ha
    have H2 := mul_le_mul hg0 (reciprocalParameter_derivative_bounds hy v v).1 (abs_nonneg _) hB
    nlinarith only [H, H1, H2]
  · apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro v
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro w
    change |fderiv ℝ (fderiv ℝ (fun z => reciprocalParameter z * f z)) y v w| ≤ _
    rw [fderiv2_mul_apply haReg hfReg]
    have H0 := mul_le_mul_of_nonneg_left (hf2 v w) ha
    have H1 := mul_le_mul (reciprocalParameter_derivative_bounds hy v w).1 (hf1 w) (abs_nonneg _) (by positivity : 0 ≤ a * ‖v‖)
    have H2 := mul_le_mul (reciprocalParameter_derivative_bounds hy w v).1 (hf1 v) (abs_nonneg _) (by positivity : 0 ≤ a * ‖w‖)
    have H3 := mul_le_mul (reciprocalParameter_derivative_bounds hy v w).2.1 hg0 (abs_nonneg _) (by positivity : 0 ≤ 2 * a * ‖v‖ * ‖w‖)
    have htri (r s t u : ℝ) : |r + s + t + u| ≤ |r| + |s| + |t| + |u| := by
      linarith only [abs_add_le r s, abs_add_le (r + s) t, abs_add_le (r + s + t) u]
    have H := htri (a * fderiv ℝ (fderiv ℝ f) y v w)
      (fderiv ℝ reciprocalParameter y v * fderiv ℝ f y w)
      (fderiv ℝ reciprocalParameter y w * fderiv ℝ f y v)
      (fderiv ℝ (fderiv ℝ reciprocalParameter) y v w * f y)
    simp only [abs_mul, abs_of_nonneg ha] at H
    nlinarith only [H, H0, H1, H2, H3]

end BianchiIX
