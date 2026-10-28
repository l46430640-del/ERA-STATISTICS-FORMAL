import BianchiIX.Dynamics.StableCenterHessianCoefficients

noncomputable section

namespace BianchiIX

def stableCenterHessianBudget (y v w : StableState) : ℝ :=
  (|y 1| + |y 2|) ^ 2 * ‖v‖ * ‖w‖ +
    (|y 1| + |y 2|) * (‖v‖ * ‖![w 1, w 2]‖ + ‖![v 1, v 2]‖ * ‖w‖) +
    ‖![v 1, v 2]‖ * ‖![w 1, w 2]‖

theorem stableCenterHessianBudget_nonneg (y v w : StableState) :
    0 ≤ stableCenterHessianBudget y v w := by unfold stableCenterHessianBudget; positivity

theorem stableRescaledHessian_center_bound {y : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 10)
    (hu : |y 1| ≤ 1 / 100) (hw : |y 2| ≤ 1 / 100) (v w : StableState) :
    |((c + 1) • stableOriginalHessian y v w) 0| ≤ 1024 * stableCenterHessianBudget y v w := by
  let K := c + 1
  let D := stableBoundaryDenom y
  let b := |y 1| + |y 2|
  let R := b ^ 2 * ‖v‖ * ‖w‖
  let S := b * (‖v‖ * ‖![w 1, w 2]‖ + ‖![v 1, v 2]‖ * ‖w‖)
  let Z := ‖![v 1, v 2]‖ * ‖![w 1, w 2]‖
  let T0 := (6 * K / D) * stableBoundaryHessian y v w 0
  let T1 := (dotProduct (stableDenomGradient y) v / D) * (K * (stableOriginalJacobian y).mulVec w 0)
  let T2 := (dotProduct (stableDenomGradient y) w / D) * (K * (stableOriginalJacobian y).mulVec v 0)
  let T3 := (stableDenomHessian v w / D) * (K * stableOriginalField y 0)
  have hD : 0 < D := stableBoundaryDenom_pos y
  have hK : 0 < K := by dsimp [K]; linarith
  have hs1 : K / D ≤ 1 := (div_le_one hD).mpr (stableBoundaryDenom_lower hc hm).2
  have hs2 : K ^ 2 / D ≤ 3 := (div_le_iff₀ hD).mpr (by nlinarith [(stableBoundaryDenom_lower hc hm).1])
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hS : 0 ≤ S := by dsimp [S, b]; positivity
  have hZ : 0 ≤ Z := by dsimp [Z]; positivity
  have hT0 : |T0| ≤ 18 * S + 144 * Z := by
    dsimp only [T0]
    rw [abs_mul, abs_of_pos (by positivity : 0 < 6 * K / D)]
    calc
      _ ≤ (6 * K / D) * (3 * S + 8 * K * Z) := by
        have H := mul_le_mul_of_nonneg_left (stableBoundaryHessian_center_bound hc hm v w)
          (show 0 ≤ 6 * K / D by positivity)
        convert! H using 1
        dsimp [S, K, Z, b]
        ring
      _ = (K / D) * (18 * S) + (K ^ 2 / D) * (48 * Z) := by ring
      _ ≤ 1 * (18 * S) + 3 * (48 * Z) :=
        add_le_add (mul_le_mul_of_nonneg_right hs1 (by positivity))
          (mul_le_mul_of_nonneg_right hs2 (by positivity))
      _ = _ := by ring
  have hT1 := stableCenterHessian_clock_bound hc hm hu hw v w
  have hT2 := stableCenterHessian_clock_bound hc hm hu hw w v
  have hT3 : |T3| ≤ 60 * R := by
    dsimp only [T3]
    rw [abs_mul, abs_div, abs_mul, abs_of_pos hD, abs_of_pos hK]
    have H := mul_le_mul (stableDenomHessian_bound v w) (stableOriginalField_center_bound hc hm)
      (abs_nonneg _) (by positivity)
    calc
      _ = (K / D) * (|stableDenomHessian v w| * |stableOriginalField y 0|) := by ring
      _ ≤ 1 * ((10 * ‖v‖ * ‖w‖) * (6 * b ^ 2)) :=
        mul_le_mul hs1 H (by positivity) (by norm_num)
      _ = _ := by dsimp [R]; ring
  have heq : ((c + 1) • stableOriginalHessian y v w) 0 = T0 - T1 - T2 - T3 := by
    rw [stableOriginalHessian_factor]
    dsimp [T0, T1, T2, T3, K, D]
    ring
  rw [heq]
  have H1 := abs_sub T0 T1
  have H2 := abs_sub (T0 - T1) T2
  have H3 := abs_sub (T0 - T1 - T2) T3
  change |T1| ≤ _ at hT1
  change |T2| ≤ _ at hT2
  dsimp [stableCenterHessianBudget, R, S, Z, b] at hT0 hT3 hR hS hZ ⊢
  nlinarith only [H1, H2, H3, hT0, hT1, hT2, hT3, hR, hS, hZ]

theorem stableCenterHessianBudget_transport {y v w : StableState} {b V W N M q : ℝ}
    (hb : 0 ≤ b) (hV : 0 ≤ V) (hW : 0 ≤ W) (hN : 0 ≤ N) (hM : 0 ≤ M)
    (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (hy : |y 1| + |y 2| ≤ b * q) (hv : ‖v‖ ≤ V) (hw : ‖w‖ ≤ W)
    (hvz : ‖![v 1, v 2]‖ ≤ N * q) (hwz : ‖![w 1, w 2]‖ ≤ M * q) :
    stableCenterHessianBudget y v w ≤ (b ^ 2 * V * W + b * (V * M + N * W) + N * M) * q := by
  have hy2 : (|y 1| + |y 2|) ^ 2 ≤ b ^ 2 * q ^ 2 := by
    have H := (sq_le_sq₀ (by positivity : 0 ≤ |y 1| + |y 2|) (mul_nonneg hb hq)).mpr hy
    nlinarith only [H]
  have H0 := mul_le_mul (mul_le_mul hy2 hv (norm_nonneg _) (by positivity)) hw (norm_nonneg _) (by positivity)
  have H1 := mul_le_mul hy
    (add_le_add (mul_le_mul hv hwz (norm_nonneg _) hV)
      (mul_le_mul hvz hw (norm_nonneg _) (mul_nonneg hN hq))) (by positivity) (mul_nonneg hb hq)
  have H2 := mul_le_mul hvz hwz (norm_nonneg _) (mul_nonneg hN hq)
  have H3 := mul_le_mul_of_nonneg_left (show q ^ 2 ≤ q by nlinarith)
    (show 0 ≤ b ^ 2 * V * W + b * (V * M + N * W) + N * M by positivity)
  unfold stableCenterHessianBudget
  nlinarith only [H0, H1, H2, H3]

end BianchiIX
