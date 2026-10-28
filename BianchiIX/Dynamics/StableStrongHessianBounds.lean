import BianchiIX.Dynamics.StableStrongHessianCoefficients

noncomputable section

namespace BianchiIX

def stableStrongHessianBudget (y v w : StableState) : ℝ :=
  |y 1| * ‖v‖ * ‖w‖ + (|v 0| * |w 1| + |v 1| * |w 0|) +
    (|y 1| + |y 2|) * (|v 1| * ‖w‖ + ‖v‖ * |w 1|)

theorem stableStrongHessianBudget_nonneg (y v w : StableState) :
    0 ≤ stableStrongHessianBudget y v w := by unfold stableStrongHessianBudget; positivity

theorem stableStrongHessian_clock_bound {y : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 10)
    (hu : |y 1| ≤ 1 / 100) (hw : |y 2| ≤ 1 / 100) (v w : StableState) :
    |(dotProduct (stableDenomGradient y) v / stableBoundaryDenom y) *
        ((c + 1) * (stableOriginalJacobian y).mulVec w 1)| ≤
      576 * |y 1| * ‖v‖ * ‖w‖ + 108 * |v 0| * |w 1| +
        72 * (|y 1| + |y 2|) * ‖v‖ * |w 1| := by
  let K := c + 1
  let D := stableBoundaryDenom y
  let b := |y 1| + |y 2|
  let d := |dotProduct (stableDenomGradient y) v| / D
  have hD : 0 < D := stableBoundaryDenom_pos y
  have hK : 0 < K := by dsimp [K]; linarith
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hs1 : K / D ≤ 1 := (div_le_one hD).mpr (stableBoundaryDenom_lower hc hm).2
  have hs2 : K ^ 2 / D ≤ 3 := (div_le_iff₀ hD).mpr (by nlinarith [(stableBoundaryDenom_lower hc hm).1])
  have hratio : d ≤ (6 * K / D) * ‖v‖ := by
    convert! div_le_div_of_nonneg_right (stableDenomGradient_bound hc hm hu hw v) hD.le using 1
    ring
  have hsplit : d ≤ (2 * K / D) * |v 0| + (4 * b / D) * ‖v‖ := by
    convert! div_le_div_of_nonneg_right (stableDenomGradient_split_bound hc hm v) hD.le using 1
    ring
  have hleft : d * (96 * |y 1| * ‖w‖) ≤ 576 * |y 1| * ‖v‖ * ‖w‖ := by
    calc
      _ ≤ ((6 * K / D) * ‖v‖) * (96 * |y 1| * ‖w‖) :=
        mul_le_mul_of_nonneg_right hratio (by positivity)
      _ = (K / D) * (576 * |y 1| * ‖v‖ * ‖w‖) := by ring
      _ ≤ 1 * (576 * |y 1| * ‖v‖ * ‖w‖) := mul_le_mul_of_nonneg_right hs1 (by positivity)
      _ = _ := one_mul _
  have hright : d * (18 * K * |w 1|) ≤ 108 * |v 0| * |w 1| + 72 * b * ‖v‖ * |w 1| := by
    calc
      _ ≤ ((2 * K / D) * |v 0| + (4 * b / D) * ‖v‖) * (18 * K * |w 1|) :=
        mul_le_mul_of_nonneg_right hsplit (by positivity)
      _ = (K ^ 2 / D) * (36 * |v 0| * |w 1|) + (K / D) * (72 * b * ‖v‖ * |w 1|) := by ring
      _ ≤ 3 * (36 * |v 0| * |w 1|) + 1 * (72 * b * ‖v‖ * |w 1|) :=
        add_le_add (mul_le_mul_of_nonneg_right hs2 (by positivity))
          (mul_le_mul_of_nonneg_right hs1 (by dsimp [b]; positivity))
      _ = _ := by ring
  rw [abs_mul, abs_div, abs_of_pos hD]
  have H := mul_le_mul_of_nonneg_left (stableRescaledJacobian_strong_apply hc hm hu hw w) hd
  change d * |(c + 1) * (stableOriginalJacobian y).mulVec w 1| ≤ _
  dsimp only [K, b] at hright H
  nlinarith only [H, hleft, hright]

theorem stableRescaledHessian_strong_bound {y : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 10)
    (hu : |y 1| ≤ 1 / 100) (hw : |y 2| ≤ 1 / 100) (v w : StableState) :
    |((c + 1) • stableOriginalHessian y v w) 1| ≤ 2048 * stableStrongHessianBudget y v w := by
  let K := c + 1
  let D := stableBoundaryDenom y
  let R := |y 1| * ‖v‖ * ‖w‖
  let T := |v 0| * |w 1| + |v 1| * |w 0|
  let S := (|y 1| + |y 2|) * (|v 1| * ‖w‖ + ‖v‖ * |w 1|)
  let T0 := (6 * K / D) * stableBoundaryHessian y v w 1
  let T1 := (dotProduct (stableDenomGradient y) v / D) * (K * (stableOriginalJacobian y).mulVec w 1)
  let T2 := (dotProduct (stableDenomGradient y) w / D) * (K * (stableOriginalJacobian y).mulVec v 1)
  let T3 := (stableDenomHessian v w / D) * (K * stableOriginalField y 1)
  have hD : 0 < D := stableBoundaryDenom_pos y
  have hK : 0 < K := by dsimp [K]; linarith
  have hs1 : K / D ≤ 1 := (div_le_one hD).mpr (stableBoundaryDenom_lower hc hm).2
  have hs2 : K ^ 2 / D ≤ 3 := (div_le_iff₀ hD).mpr (by nlinarith [(stableBoundaryDenom_lower hc hm).1])
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hT0 : |T0| ≤ 30 * R + 18 * T + 6 * S := by
    dsimp only [T0]
    rw [abs_mul, abs_of_pos (by positivity : 0 < 6 * K / D)]
    calc
      _ ≤ (6 * K / D) * (5 * R + K * T + S) := by
        have H := mul_le_mul_of_nonneg_left (stableBoundaryHessian_strong_bound hc hm v w)
          (show 0 ≤ 6 * K / D by positivity)
        convert! H using 1
        dsimp [R, K, T, S]
        ring
      _ = (K / D) * (30 * R + 6 * S) + (K ^ 2 / D) * (6 * T) := by ring
      _ ≤ 1 * (30 * R + 6 * S) + 3 * (6 * T) :=
        add_le_add (mul_le_mul_of_nonneg_right hs1 (by positivity))
          (mul_le_mul_of_nonneg_right hs2 (by positivity))
      _ = _ := by ring
  have hT1 := stableStrongHessian_clock_bound hc hm hu hw v w
  have hT2 := stableStrongHessian_clock_bound hc hm hu hw w v
  have hT3 : |T3| ≤ 60 * R := by
    dsimp only [T3]
    rw [abs_mul, abs_div, abs_mul, abs_of_pos hD, abs_of_pos hK]
    have H := mul_le_mul (stableDenomHessian_bound v w) (stableOriginalField_strong_bound hc hm hu hw)
      (abs_nonneg _) (by positivity)
    calc
      _ = (K / D) * (|stableDenomHessian v w| * |stableOriginalField y 1|) := by ring
      _ ≤ 1 * ((10 * ‖v‖ * ‖w‖) * (6 * |y 1|)) :=
        mul_le_mul hs1 H (by positivity) (by norm_num)
      _ = _ := by dsimp [R]; ring
  have heq : ((c + 1) • stableOriginalHessian y v w) 1 = T0 - T1 - T2 - T3 := by
    rw [stableOriginalHessian_factor]
    dsimp [T0, T1, T2, T3, K, D]
    ring
  rw [heq]
  have H1 := abs_sub T0 T1
  have H2 := abs_sub (T0 - T1) T2
  have H3 := abs_sub (T0 - T1 - T2) T3
  change |T1| ≤ _ at hT1
  change |T2| ≤ _ at hT2
  dsimp [stableStrongHessianBudget, R, T, S] at hT0 hT3 hR hT hS ⊢
  nlinarith only [H1, H2, H3, hT0, hT1, hT2, hT3, hR, hT, hS]

end BianchiIX
