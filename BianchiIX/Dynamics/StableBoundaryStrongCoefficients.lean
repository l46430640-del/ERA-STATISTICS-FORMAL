import BianchiIX.Dynamics.StableBoundaryCoupling

noncomputable section

namespace BianchiIX

theorem stableRescaledJacobian_strong_diagonal {y : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 10)
    (hu : |y 1| ≤ 1 / 100) (hw : |y 2| ≤ 1 / 100) :
    (c + 1) * stableOriginalJacobian y 1 1 ≤ -3 * (c + 1) / 16 := by
  have H := (stableRescaledJacobian_stable_rows hc hm hu hw).1
  have hK : 0 ≤ c + 1 := by linarith
  nlinarith only [H, mul_nonneg hK (abs_nonneg (stableOriginalJacobian y 1 2))]

theorem stableRescaledJacobian_strong_weak {y : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 10)
    (hu : |y 1| ≤ 1 / 100) (hw : |y 2| ≤ 1 / 100) :
    |(c + 1) * stableOriginalJacobian y 1 2| ≤ 18 * |y 1| * (|y 1| + |y 2|) := by
  have hK : 0 < c + 1 := by linarith
  have hD := stableBoundaryDenom_pos y
  have hscale : (c + 1) * (6 / stableBoundaryDenom y) ≤ 6 := by
    have H := (stableBoundaryDenom_lower hc hm).2
    rw [show (c + 1) * (6 / stableBoundaryDenom y) =
      (6 * (c + 1)) / stableBoundaryDenom y by ring]
    apply (div_le_iff₀ hD).mpr
    linarith
  have hg : |stableDenomGradient y 2| ≤ 2 * (|y 1| + |y 2|) := by
    change |2 * (y 2 - y 1)| ≤ _
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have H := abs_sub (y 2) (y 1)
    linarith
  have hf := (stableBoundary_field_div_bounds hc hm hu hw).1
  have hprod : |stableBoundaryField y 1 / stableBoundaryDenom y * stableDenomGradient y 2| ≤
      2 * |y 1| * (|y 1| + |y 2|) := by
    rw [abs_mul]
    nlinarith only [mul_le_mul hf hg (abs_nonneg _) (abs_nonneg _)]
  have hp : |stableBoundaryJacobian y 1 2| ≤ |y 1| * (|y 1| + |y 2|) := by
    change |-y 1 * y 2| ≤ _
    rw [abs_mul, abs_neg]
    nlinarith [sq_nonneg |y 1|]
  have hb : |stableBoundaryJacobian y 1 2 -
      stableBoundaryField y 1 / stableBoundaryDenom y * stableDenomGradient y 2| ≤
        3 * |y 1| * (|y 1| + |y 2|) := by
    have H := abs_sub (stableBoundaryJacobian y 1 2)
      (stableBoundaryField y 1 / stableBoundaryDenom y * stableDenomGradient y 2)
    linarith
  rw [stableOriginalJacobian_factor, abs_mul, abs_of_pos hK, abs_mul,
    abs_of_pos (by positivity : 0 < 6 / stableBoundaryDenom y), ← mul_assoc]
  have H := mul_le_mul hscale hb (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 6)
  nlinarith only [H]

end BianchiIX
