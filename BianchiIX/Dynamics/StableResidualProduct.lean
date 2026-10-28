import BianchiIX.Dynamics.StableScaledResidualDerivatives

noncomputable section

namespace BianchiIX

/-- A bounded smooth factor preserves the strong-wall factor and all quartic input weights. -/
theorem stableResidual_product_bounds {f g : StableState → ℝ} {y : StableState} {B : ℝ}
    (hB : 0 ≤ B) (hf : ContDiffAt ℝ 2 f y) (hg : ContDiffAt ℝ 2 g y)
    (hf0 : |f y| ≤ 1) (hf1 : ∀ v, |fderiv ℝ f y v| ≤ ‖v‖)
    (hf2 : ∀ v w, |fderiv ℝ (fderiv ℝ f) y v w| ≤ ‖v‖ * ‖w‖)
    (hg0 : |g y| ≤ B * |y 1| * (|y 1| + |y 2|) ^ 3)
    (hg1 : ∀ v, |fderiv ℝ g y v| ≤
      B * (|v 1| * (|y 1| + |y 2|) ^ 3 + |y 1| * stableCubicFirstBudget y v))
    (hg2 : ∀ v w, |fderiv ℝ (fderiv ℝ g) y v w| ≤
      B * (|v 1| * stableCubicFirstBudget y w + |w 1| * stableCubicFirstBudget y v +
        |y 1| * stableCubicSecondBudget y v w)) :
    |f y * g y| ≤ 4 * B * |y 1| * (|y 1| + |y 2|) ^ 3 ∧
      (∀ v, |fderiv ℝ (fun z => f z * g z) y v| ≤
        4 * B * (|v 1| * (|y 1| + |y 2|) ^ 3 + |y 1| * stableCubicFirstBudget y v)) ∧
      (∀ v w, |fderiv ℝ (fderiv ℝ (fun z => f z * g z)) y v w| ≤
        4 * B * (|v 1| * stableCubicFirstBudget y w + |w 1| * stableCubicFirstBudget y v +
          |y 1| * stableCubicSecondBudget y v w)) := by
  let b := |y 1| + |y 2|
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hc1 (v : StableState) : b ^ 3 * ‖v‖ ≤ stableCubicFirstBudget y v := by
    unfold stableCubicFirstBudget
    exact le_add_of_nonneg_right (by positivity)
  have hc20 (v w : StableState) : b ^ 3 * ‖v‖ * ‖w‖ ≤ stableCubicSecondBudget y v w := by
    unfold stableCubicSecondBudget
    have h1 : 0 ≤ 3 * b ^ 2 * (‖v‖ * ‖![w 1, w 2]‖ + ‖![v 1, v 2]‖ * ‖w‖) := by positivity
    have h2 : 0 ≤ 6 * b * ‖![v 1, v 2]‖ * ‖![w 1, w 2]‖ := by positivity
    nlinarith only [h1, h2]
  have hc21 (v w : StableState) : ‖v‖ * stableCubicFirstBudget y w ≤ stableCubicSecondBudget y v w := by
    unfold stableCubicFirstBudget stableCubicSecondBudget
    have h1 : 0 ≤ 3 * b ^ 2 * ‖![v 1, v 2]‖ * ‖w‖ := by positivity
    have h2 : 0 ≤ 6 * b * ‖![v 1, v 2]‖ * ‖![w 1, w 2]‖ := by positivity
    nlinarith only [h1, h2]
  have hc22 (v w : StableState) : ‖w‖ * stableCubicFirstBudget y v ≤ stableCubicSecondBudget y v w := by
    unfold stableCubicFirstBudget stableCubicSecondBudget
    have h1 : 0 ≤ 3 * b ^ 2 * ‖v‖ * ‖![w 1, w 2]‖ := by positivity
    have h2 : 0 ≤ 6 * b * ‖![v 1, v 2]‖ * ‖![w 1, w 2]‖ := by positivity
    nlinarith only [h1, h2]
  refine ⟨?_, ?_, ?_⟩
  · rw [abs_mul]
    have H := mul_le_mul hf0 hg0 (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    nlinarith only [H, show 0 ≤ B * |y 1| * b ^ 3 by positivity]
  · intro v
    rw [fderiv_fun_mul (hf.differentiableAt (by norm_num)) (hg.differentiableAt (by norm_num))]
    change |f y * fderiv ℝ g y v + g y * fderiv ℝ f y v| ≤ _
    have H := abs_add_le (f y * fderiv ℝ g y v) (g y * fderiv ℝ f y v)
    simp only [abs_mul] at H
    have H0 := mul_le_mul hf0 (hg1 v) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    have H1 := mul_le_mul hg0 (hf1 v) (abs_nonneg _) (by positivity)
    have T := mul_le_mul_of_nonneg_left (hc1 v) (show 0 ≤ B * |y 1| by positivity)
    have hpos1 := stableCubicFirstBudget_nonneg y v
    nlinarith only [H, H0, H1, T, show 0 ≤ B * |v 1| * b ^ 3 by positivity,
      show 0 ≤ B * |y 1| * stableCubicFirstBudget y v by positivity]
  · intro v w
    rw [fderiv2_mul_apply hf hg]
    have H0 := mul_le_mul hf0 (hg2 v w) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    have H1 := mul_le_mul (hf1 v) (hg1 w) (abs_nonneg _) (norm_nonneg v)
    have H2 := mul_le_mul (hf1 w) (hg1 v) (abs_nonneg _) (norm_nonneg w)
    have H3 := mul_le_mul (hf2 v w) hg0 (abs_nonneg _) (by positivity)
    have T1 := mul_le_mul_of_nonneg_left (hc1 v) (show 0 ≤ B * |w 1| by positivity)
    have T2 := mul_le_mul_of_nonneg_left (hc1 w) (show 0 ≤ B * |v 1| by positivity)
    have T3 := mul_le_mul_of_nonneg_left (hc21 v w) (show 0 ≤ B * |y 1| by positivity)
    have T4 := mul_le_mul_of_nonneg_left (hc22 v w) (show 0 ≤ B * |y 1| by positivity)
    have T5 := mul_le_mul_of_nonneg_left (hc20 v w) (show 0 ≤ B * |y 1| by positivity)
    have htri (a b c d : ℝ) : |a + b + c + d| ≤ |a| + |b| + |c| + |d| := by
      linarith only [abs_add_le a b, abs_add_le (a + b) c, abs_add_le (a + b + c) d]
    have H := htri (f y * fderiv ℝ (fderiv ℝ g) y v w)
      (fderiv ℝ f y v * fderiv ℝ g y w) (fderiv ℝ f y w * fderiv ℝ g y v)
      (fderiv ℝ (fderiv ℝ f) y v w * g y)
    simp only [abs_mul] at H
    have hv := stableCubicFirstBudget_nonneg y v
    have hw := stableCubicFirstBudget_nonneg y w
    nlinarith only [H, H0, H1, H2, H3, T1, T2, T3, T4, T5,
      show 0 ≤ B * |v 1| * stableCubicFirstBudget y w by positivity,
      show 0 ≤ B * |w 1| * stableCubicFirstBudget y v by positivity]

end BianchiIX
