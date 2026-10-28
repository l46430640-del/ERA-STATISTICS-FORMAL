import BianchiIX.Dynamics.StableScaledResidualCubic

noncomputable section

namespace BianchiIX

theorem stableScaledResidual_contDiffAt {K : ℝ} {y : StableState}
    (hg : ContDiffAt ℝ 2 (stableScaledResidualCubic K) y) :
    ContDiffAt ℝ 2 (stableScaledResidual K) y := by
  have heq : stableScaledResidual K = fun z => z 1 * stableScaledResidualCubic K z :=
    funext (stableScaledResidual_factor K)
  rw [heq]
  exact (contDiffAt_apply ℝ ℝ 1 y).mul hg

theorem stableScaledResidual_fderiv {K : ℝ} {y : StableState}
    (hg : ContDiffAt ℝ 2 (stableScaledResidualCubic K) y) (v : StableState) :
    fderiv ℝ (stableScaledResidual K) y v =
      v 1 * stableScaledResidualCubic K y + y 1 * fderiv ℝ (stableScaledResidualCubic K) y v := by
  have heq : stableScaledResidual K = fun z => z 1 * stableScaledResidualCubic K z :=
    funext (stableScaledResidual_factor K)
  rw [heq, fderiv_fun_mul ((contDiffAt_apply (n := 1) ℝ ℝ 1 y).differentiableAt (by norm_num))
    (hg.differentiableAt (by norm_num))]
  have hp : fderiv ℝ (fun z : StableState => z 1) y =
      (ContinuousLinearMap.proj 1 : StableState →L[ℝ] ℝ) :=
    (ContinuousLinearMap.proj 1 : StableState →L[ℝ] ℝ).fderiv
  rw [hp]
  change y 1 * fderiv ℝ (stableScaledResidualCubic K) y v + stableScaledResidualCubic K y * v 1 = _
  ring

theorem stableScaledResidual_fderiv2 {K : ℝ} {y : StableState}
    (hg : ContDiffAt ℝ 2 (stableScaledResidualCubic K) y) (v w : StableState) :
    fderiv ℝ (fderiv ℝ (stableScaledResidual K)) y v w =
      v 1 * fderiv ℝ (stableScaledResidualCubic K) y w +
        w 1 * fderiv ℝ (stableScaledResidualCubic K) y v +
        y 1 * fderiv ℝ (fderiv ℝ (stableScaledResidualCubic K)) y v w := by
  have heq : stableScaledResidual K = fun z => z 1 * stableScaledResidualCubic K z :=
    funext (stableScaledResidual_factor K)
  rw [heq, fderiv2_mul_apply (contDiffAt_apply ℝ ℝ 1 y) hg]
  have hp : fderiv ℝ (fun z : StableState => z 1) =
      fun _ => (ContinuousLinearMap.proj 1 : StableState →L[ℝ] ℝ) :=
    funext (fun _ => (ContinuousLinearMap.proj 1 : StableState →L[ℝ] ℝ).fderiv)
  simp only [hp, fderiv_const_apply, zero_apply, zero_mul, add_zero]
  change y 1 * fderiv ℝ (fderiv ℝ (stableScaledResidualCubic K)) y v w +
    v 1 * fderiv ℝ (stableScaledResidualCubic K) y w +
    w 1 * fderiv ℝ (stableScaledResidualCubic K) y v = _
  ring

theorem stableScaledResidual_bounds_of_cubic {K B : ℝ} {y : StableState}
    (hg : ContDiffAt ℝ 2 (stableScaledResidualCubic K) y)
    (h0 : |stableScaledResidualCubic K y| ≤ B * (|y 1| + |y 2|) ^ 3)
    (h1 : ∀ v, |fderiv ℝ (stableScaledResidualCubic K) y v| ≤ B * stableCubicFirstBudget y v)
    (h2 : ∀ v w, |fderiv ℝ (fderiv ℝ (stableScaledResidualCubic K)) y v w| ≤ B * stableCubicSecondBudget y v w) :
    |stableScaledResidual K y| ≤ B * |y 1| * (|y 1| + |y 2|) ^ 3 ∧
      (∀ v, |fderiv ℝ (stableScaledResidual K) y v| ≤
        B * (|v 1| * (|y 1| + |y 2|) ^ 3 + |y 1| * stableCubicFirstBudget y v)) ∧
      (∀ v w, |fderiv ℝ (fderiv ℝ (stableScaledResidual K)) y v w| ≤
        B * (|v 1| * stableCubicFirstBudget y w + |w 1| * stableCubicFirstBudget y v +
          |y 1| * stableCubicSecondBudget y v w)) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [stableScaledResidual_factor, abs_mul]
    have H := mul_le_mul_of_nonneg_left h0 (abs_nonneg (y 1))
    nlinarith only [H]
  · intro v
    rw [stableScaledResidual_fderiv hg]
    have H := abs_add_le (v 1 * stableScaledResidualCubic K y)
      (y 1 * fderiv ℝ (stableScaledResidualCubic K) y v)
    simp only [abs_mul] at H
    have H0 := mul_le_mul_of_nonneg_left h0 (abs_nonneg (v 1))
    have H1 := mul_le_mul_of_nonneg_left (h1 v) (abs_nonneg (y 1))
    nlinarith only [H, H0, H1]
  · intro v w
    rw [stableScaledResidual_fderiv2 hg]
    have htri (a b c : ℝ) : |a + b + c| ≤ |a| + |b| + |c| := by
      linarith only [abs_add_le a b, abs_add_le (a + b) c]
    have H := htri (v 1 * fderiv ℝ (stableScaledResidualCubic K) y w)
      (w 1 * fderiv ℝ (stableScaledResidualCubic K) y v)
      (y 1 * fderiv ℝ (fderiv ℝ (stableScaledResidualCubic K)) y v w)
    simp only [abs_mul] at H
    have H0 := mul_le_mul_of_nonneg_left (h1 w) (abs_nonneg (v 1))
    have H1 := mul_le_mul_of_nonneg_left (h1 v) (abs_nonneg (w 1))
    have H2 := mul_le_mul_of_nonneg_left (h2 v w) (abs_nonneg (y 1))
    nlinarith only [H, H0, H1, H2]

theorem exists_stableScaledResidual_derivative_bounds :
    ∃ C > (0 : ℝ), ∀ (c : ℝ) (y : StableState), 2 ≤ c → |y 0 - c| ≤ 1 / 10 →
      |y 1| ≤ 1 / 100 → |y 2| ≤ 1 / 100 →
      ContDiffAt ℝ 2 (stableScaledResidual (c + 1)) y ∧
        |stableScaledResidual (c + 1) y| ≤ C / (c + 1) ^ 2 * |y 1| * (|y 1| + |y 2|) ^ 3 ∧
        (∀ v, |fderiv ℝ (stableScaledResidual (c + 1)) y v| ≤
          C / (c + 1) ^ 2 * (|v 1| * (|y 1| + |y 2|) ^ 3 + |y 1| * stableCubicFirstBudget y v)) ∧
        (∀ v w, |fderiv ℝ (fderiv ℝ (stableScaledResidual (c + 1))) y v w| ≤
          C / (c + 1) ^ 2 * (|v 1| * stableCubicFirstBudget y w + |w 1| * stableCubicFirstBudget y v +
            |y 1| * stableCubicSecondBudget y v w)) := by
  obtain ⟨C, hC, HC⟩ := exists_stableScaledResidualCubic_bounds
  refine ⟨C, hC, ?_⟩
  intro c y hc hm hu hw
  obtain ⟨hg, h0, h1, h2⟩ := HC c y hc hm hu hw
  exact ⟨stableScaledResidual_contDiffAt hg,
    stableScaledResidual_bounds_of_cubic hg h0 h1 h2⟩

end BianchiIX
