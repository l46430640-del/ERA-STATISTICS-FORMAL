import BianchiIX.Dynamics.StableStrongHessianBounds
import BianchiIX.Dynamics.StableBoundaryCenterVariation

noncomputable section

namespace BianchiIX

theorem stableRescaledDifferential_center_bound {y : StableState} {c s : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 40)
    (hu : |y 1| ≤ 1 / 200) (hw : |y 2| ≤ 1 / 200) (hs : 0 ≤ s) (v : StableState) :
    |stableRescaledDifferential (c + 1) y s v 0| ≤ |v 0| +
      1000 * (|y 1| + |y 2|) * Real.exp (512 * (|y 1| + |y 2|)) * ‖v‖ := by
  let b := |y 1| + |y 2|
  let E := Real.exp (512 * b)
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hb1 : b ≤ 1 / 100 := by dsimp [b]; linarith
  have hE : 1 ≤ E := Real.one_le_exp (by positivity)
  have H0 := (stableTangent_split_bounds v).2.2
  have H1 := mul_le_mul_of_nonneg_left H0 hb
  have H2 := mul_le_mul_of_nonneg_right hE (show 0 ≤ b * ‖v‖ by positivity)
  have H3 := mul_le_mul_of_nonneg_right hb1 (show 0 ≤ b * E * ‖v‖ by positivity)
  have H := stableRescaledDifferential_center_drift hc hm hu hw hs v
  have H' := abs_sub_abs_le_abs_sub (stableRescaledDifferential (c + 1) y s v 0) (v 0)
  dsimp only [stableVariationCenterBudget] at H
  change |stableRescaledDifferential (c + 1) y s v 0| ≤ |v 0| + 1000 * b * E * ‖v‖
  change |stableRescaledDifferential (c + 1) y s v 0 - v 0| ≤
    2 * (128 * b * ‖![v 1, v 2]‖ + 33000 * b ^ 2 * E * ‖v‖) at H
  nlinarith only [H, H', H1, H2, H3, mul_nonneg hb (mul_nonneg (Real.exp_pos (512 * b)).le (norm_nonneg v))]

theorem stableRescaledDifferential_strong_budget {y : StableState} {c s : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 40)
    (hu : |y 1| ≤ 1 / 200) (hw : |y 2| ≤ 1 / 200) (hs : 0 ≤ s) (v : StableState) :
    |stableRescaledDifferential (c + 1) y s v 1| ≤
      (|v 1| + 200 * |y 1| * Real.exp (512 * (|y 1| + |y 2|)) * ‖v‖) *
        Real.exp (-3 * (c + 1) / 16 * s) := by
  have hK : 0 < c + 1 := by linarith
  have hcoef : 512 * |y 1| * Real.exp (512 * (|y 1| + |y 2|)) * ‖v‖ / (c + 1) ≤
      200 * |y 1| * Real.exp (512 * (|y 1| + |y 2|)) * ‖v‖ := by
    apply (div_le_iff₀ hK).mpr
    nlinarith only [mul_le_mul_of_nonneg_right (show (512 : ℝ) ≤ 200 * (c + 1) by linarith)
      (show 0 ≤ |y 1| * Real.exp (512 * (|y 1| + |y 2|)) * ‖v‖ by positivity)]
  exact (stableRescaledDifferential_strong_decay hc hm hu hw hs v).trans
    (mul_le_mul_of_nonneg_right (add_le_add (le_refl _) hcoef) (Real.exp_pos _).le)

theorem stableStrongHessianBudget_transport {y v w : StableState} {a b : StableState}
    {E q : ℝ} (hE : 1 ≤ E) (hq : 0 ≤ q) (hu : |y 1| ≤ 1 / 200) (hw : |y 2| ≤ 1 / 200)
    (ha : ‖a‖ ≤ E * ‖v‖) (hb : ‖b‖ ≤ E * ‖w‖)
    (ha0 : |a 0| ≤ |v 0| + 1000 * (|y 1| + |y 2|) * E * ‖v‖)
    (hb0 : |b 0| ≤ |w 0| + 1000 * (|y 1| + |y 2|) * E * ‖w‖)
    (ha1 : |a 1| ≤ (|v 1| + 200 * |y 1| * E * ‖v‖) * q)
    (hb1 : |b 1| ≤ (|w 1| + 200 * |y 1| * E * ‖w‖) * q)
    {z : StableState} (hz1 : |z 1| ≤ |y 1| * q) (hzb : |z 1| + |z 2| ≤ |y 1| + |y 2|) :
    stableStrongHessianBudget z a b ≤ 5000 * E ^ 2 * stableStrongHessianBudget y v w * q := by
  let u := |y 1|
  let B := |y 1| + |y 2|
  let V := ‖v‖
  let W := ‖w‖
  let R := u * V * W
  let T := |v 0| * |w 1| + |v 1| * |w 0|
  let S := B * (|v 1| * W + V * |w 1|)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hB1 : B ≤ 1 / 100 := by dsimp [B]; linarith
  have hE0 : 0 ≤ E := by linarith
  have hE2 : E ≤ E ^ 2 := by nlinarith
  have hE21 : 1 ≤ E ^ 2 := by nlinarith
  have hR : 0 ≤ R := by dsimp [R, u, V, W]; positivity
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hS : 0 ≤ S := by dsimp [S, B, V, W]; positivity
  have hcent : |v 0| * W + V * |w 0| ≤ 2 * V * W := by
    have Hv : |v 0| ≤ V := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm v 0
    have Hw : |w 0| ≤ W := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm w 0
    nlinarith only [mul_le_mul_of_nonneg_right Hv (norm_nonneg w),
      mul_le_mul_of_nonneg_left Hw (norm_nonneg v)]
  have HC := mul_le_mul_of_nonneg_left hcent (show 0 ≤ 200 * u * E by dsimp [u]; positivity)
  have HR := mul_le_mul_of_nonneg_right hB1 (show 0 ≤ 400400 * E ^ 2 * R by positivity)
  have HE := mul_le_mul_of_nonneg_right hE2 hR
  have HT := mul_le_mul_of_nonneg_right hE21 hT
  have HS := mul_le_mul_of_nonneg_right hE2 hS
  have hpoly : u * E ^ 2 * V * W +
      (|v 0| + 1000 * B * E * V) * (|w 1| + 200 * u * E * W) +
      (|v 1| + 200 * u * E * V) * (|w 0| + 1000 * B * E * W) +
      B * ((|v 1| + 200 * u * E * V) * E * W + E * V * (|w 1| + 200 * u * E * W)) ≤
        5000 * E ^ 2 * (R + T + S) := by
    have heq : u * E ^ 2 * V * W +
        (|v 0| + 1000 * B * E * V) * (|w 1| + 200 * u * E * W) +
        (|v 1| + 200 * u * E * V) * (|w 0| + 1000 * B * E * W) +
        B * ((|v 1| + 200 * u * E * V) * E * W + E * V * (|w 1| + 200 * u * E * W)) =
      E ^ 2 * R + T + 1001 * E * S + 200 * u * E * (|v 0| * W + V * |w 0|) +
        400400 * B * E ^ 2 * R := by dsimp [R, T, S]; ring
    rw [heq]
    have HC' : 200 * u * E * (|v 0| * W + V * |w 0|) ≤ 400 * E * R := by
      convert! HC using 1
      dsimp [R]
      ring
    nlinarith only [HC', HR, HE, HT, HS, mul_nonneg (sq_nonneg E) hR,
      mul_nonneg (sq_nonneg E) hT, mul_nonneg (sq_nonneg E) hS]
  have H0 := mul_le_mul (mul_le_mul hz1 ha (norm_nonneg _) (by positivity)) hb (norm_nonneg _) (by positivity)
  have H1 := mul_le_mul ha0 hb1 (abs_nonneg _) (by positivity)
  have H2 := mul_le_mul ha1 hb0 (abs_nonneg _) (by positivity)
  have H3 := mul_le_mul hzb
    (add_le_add (mul_le_mul ha1 hb (norm_nonneg _) (by positivity))
      (mul_le_mul ha hb1 (abs_nonneg _) (by positivity))) (by positivity) (by positivity)
  have HP := mul_le_mul_of_nonneg_right hpoly hq
  dsimp [stableStrongHessianBudget, R, T, S, u, B, V, W] at HP ⊢
  nlinarith only [H0, H1, H2, H3, HP]

end BianchiIX
