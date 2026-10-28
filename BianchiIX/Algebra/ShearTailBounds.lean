import BianchiIX.Algebra.SectionBounds

noncomputable section

namespace BianchiIX

/-- The small growing-wall tail has a quadratic projection denominator. -/
theorem shearTail_constraint_bounds {a p s n x y : ℝ}
    (ha : 0 < a ∧ a ≤ 1 / 256) (hp : p < 0)
    (hs : a / 2 ≤ s ∧ s ≤ 3 * a)
    (hn : 0 ≤ n ∧ n ≤ a ^ 2) (hx : 0 ≤ x ∧ x ≤ a ^ 2)
    (hy : 0 ≤ y ∧ y ≤ a / 16) (hc : constraint p s n x y = 1) :
    |curvature n x y| ≤ a ^ 2 / 128 ∧
      a ^ 2 / 5 ≤ 1 - p ^ 2 ∧ 1 - p ^ 2 ≤ 10 * a ^ 2 ∧
      -1 < p ∧ p ≤ -(15 / 16) ∧
      a ^ 2 / 10 ≤ 1 + p ∧ 1 + p ≤ 6 * a ^ 2 := by
  have ha2 : a ^ 2 ≤ a / 256 := by nlinarith only [ha.1, ha.2]
  have hsum : n + x + y ≤ 9 * a / 128 := by linarith only [hn.2, hx.2, hy.2, ha2]
  have hsum2 := pow_le_pow_left₀ (by positivity [hn.1, hx.1, hy.1] : 0 ≤ n + x + y) hsum 2
  have hQ : |curvature n x y| ≤ a ^ 2 / 128 :=
    (curvature_abs_le_sum_sq hn.1 hx.1 hy.1).trans (by nlinarith only [hsum2, sq_nonneg a])
  have hs0 : 0 ≤ s := by linarith only [hs.1, ha.1]
  have hslo := pow_le_pow_left₀ (div_nonneg ha.1.le (by norm_num) : 0 ≤ a / 2) hs.1 2
  have hshi := pow_le_pow_left₀ hs0 hs.2 2
  have HC : p ^ 2 + s ^ 2 + curvature n x y = 1 := hc
  have hlo : a ^ 2 / 5 ≤ 1 - p ^ 2 := by nlinarith only [HC, hslo, (abs_le.mp hQ).1, sq_nonneg a]
  have hhi : 1 - p ^ 2 ≤ 10 * a ^ 2 := by nlinarith only [HC, hshi, (abs_le.mp hQ).2, sq_nonneg a]
  have hplo : -1 < p := by nlinarith only [hlo, ha.1, hp]
  have hphi : p ≤ -(15 / 16) := by
    have haSq := pow_le_pow_left₀ ha.1.le ha.2 2
    nlinarith only [hhi, haSq, hp, sq_nonneg (p + 15 / 16)]
  refine ⟨hQ, hlo, hhi, hplo, hphi, ?_, ?_⟩
  · nlinarith only [hlo, sq_nonneg (1 + p)]
  · have H := mul_le_mul_of_nonneg_right (show (5 : ℝ) / 3 ≤ 1 - p by linarith only [hphi])
      (show 0 ≤ 1 + p by linarith only [hplo])
    nlinarith only [H, hhi]

theorem shearTail_wall_rates {a p s n x y : ℝ}
    (ha : 0 < a ∧ a ≤ 1 / 256) (hp : p < 0)
    (hs : a / 2 ≤ s ∧ s ≤ 3 * a)
    (hn : 0 ≤ n ∧ n ≤ a ^ 2) (hx : 0 ≤ x ∧ x ≤ a ^ 2)
    (hy : 0 ≤ y ∧ y ≤ a / 16) (hc : constraint p s n x y = 1) :
    rateOne p s ≤ -2 ∧ |rateTwo p s| ≤ 6 * a ∧ rateThree p s ≤ -a / 2 := by
  obtain ⟨hQ, _, _, _, hp', hAl, hAu⟩ := shearTail_constraint_bounds ha hp hs hn hx hy hc
  have HC : p ^ 2 + s ^ 2 + curvature n x y = 1 := hc
  have ha2 : a ^ 2 ≤ a / 256 := by nlinarith only [ha.1, ha.2]
  have hs0 : 0 ≤ s := by linarith only [hs.1, ha.1]
  have hr0 := Real.sqrt_nonneg (3 : ℝ)
  have hr2 := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have hrl : (3 : ℝ) / 2 ≤ Real.sqrt 3 := by nlinarith only [hr0, hr2]
  have hru : Real.sqrt 3 ≤ (7 : ℝ) / 4 := by nlinarith only [hr0, hr2]
  have hRslo := mul_le_mul hrl hs.1 (div_nonneg ha.1.le (by norm_num) : 0 ≤ a / 2) hr0
  have hRshi := mul_le_mul hru hs.2 hs0 (by norm_num : (0 : ℝ) ≤ 7 / 4)
  refine ⟨?_, abs_le.mpr ⟨?_, ?_⟩, ?_⟩
  · dsimp only [rateOne, shearSq]
    nlinarith only [hp', sq_nonneg (p + 15 / 16), sq_nonneg s]
  · dsimp only [rateTwo, shearSq]
    nlinarith only [HC, (abs_le.mp hQ).1, hAu, hRslo, ha2, ha.1]
  · dsimp only [rateTwo, shearSq]
    nlinarith only [HC, (abs_le.mp hQ).2, hAl, hRshi, ha2, ha.1, sq_nonneg a]
  · dsimp only [rateThree, shearSq]
    nlinarith only [HC, (abs_le.mp hQ).2, hAl, hRslo, ha2, ha.1, sq_nonneg a]

/-- Keeping the strong-wall square separate avoids a long-time shear loss. -/
theorem shearTail_shear_rate {a s n x y : ℝ}
    (ha : 0 ≤ a ∧ a ≤ 1 / 256) (hs : |s| ≤ 3 * a)
    (hn : 0 ≤ n) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |shearMinus s n x y| ≤ 3 * (x ^ 2 + y ^ 2 + n * (x + y) + a * n ^ 2) := by
  have hQ : |curvature n x y| ≤ n ^ 2 + x ^ 2 + y ^ 2 + 2 * n * (x + y) := by
    apply abs_le.mpr
    dsimp only [curvature]
    constructor
    · nlinarith only [sq_nonneg n, sq_nonneg (x - y)]
    · nlinarith only [mul_nonneg hx hy, mul_nonneg hn (add_nonneg hx hy)]
  have hH : |-x ^ 2 + y ^ 2 + n * x - n * y| ≤ x ^ 2 + y ^ 2 + n * (x + y) := by
    apply abs_le.mpr
    constructor <;> nlinarith only [sq_nonneg x, sq_nonneg y, mul_nonneg hn hx, mul_nonneg hn hy]
  have hr : |Real.sqrt 3| ≤ (2 : ℝ) := by
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    nlinarith only [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg (3 : ℝ)]
  have HQ := mul_le_mul hQ hs (abs_nonneg _) (by positivity : 0 ≤ n ^ 2 + x ^ 2 + y ^ 2 + 2 * n * (x + y))
  have HH := mul_le_mul hr hH (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
  have H := abs_add_le (curvature n x y * s) (Real.sqrt 3 * (-x ^ 2 + y ^ 2 + n * x - n * y))
  rw [abs_mul, abs_mul] at H
  have Hsmall := mul_nonneg (show 0 ≤ 1 - 6 * a by linarith only [ha.2])
    (show 0 ≤ x ^ 2 + y ^ 2 + n * (x + y) by positivity)
  dsimp only [shearMinus]
  nlinarith only [H, HQ, HH, Hsmall, mul_nonneg ha.1 (add_nonneg (sq_nonneg x) (sq_nonneg y))]

end BianchiIX
