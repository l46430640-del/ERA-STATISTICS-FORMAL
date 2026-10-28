import BianchiIX.Dynamics.StableScaledResidualCubic
import BianchiIX.Dynamics.StableHessianPolynomialBounds

noncomputable section

namespace BianchiIX

def stableFirstInputWeight (b : ℝ) (v : StableState) : ℝ :=
  b * ‖v‖ + ‖![v 1, v 2]‖

def stableSecondInputWeight (b : ℝ) (v w : StableState) : ℝ :=
  b * ‖v‖ * ‖w‖ + ‖![v 1, v 2]‖ * ‖w‖ + ‖v‖ * ‖![w 1, w 2]‖

theorem stableFirstInputWeight_nonneg {b : ℝ} (hb : 0 ≤ b) (v : StableState) :
    0 ≤ stableFirstInputWeight b v := by unfold stableFirstInputWeight; positivity

theorem stableSecondInputWeight_nonneg {b : ℝ} (hb : 0 ≤ b) (v w : StableState) :
    0 ≤ stableSecondInputWeight b v w := by unfold stableSecondInputWeight; positivity

theorem stableFirstInputWeight_center (b : ℝ) {v : StableState} (hv1 : v 1 = 0) (hv2 : v 2 = 0) :
    stableFirstInputWeight b v = b * ‖v‖ := by simp [stableFirstInputWeight, hv1, hv2]

theorem stableFirstInputWeight_le {b : ℝ} (hb : b ≤ 1) (v : StableState) :
    stableFirstInputWeight b v ≤ 2 * ‖v‖ := by
  have H := mul_le_mul_of_nonneg_right hb (norm_nonneg v)
  have Hz := (stableTangent_split_bounds v).2.2
  unfold stableFirstInputWeight
  linarith

theorem stableSecondInputWeight_product (b : ℝ) (v w : StableState) :
    b * stableSecondInputWeight b v w ≤ stableFirstInputWeight b v * stableFirstInputWeight b w := by
  unfold stableSecondInputWeight stableFirstInputWeight
  nlinarith only [mul_nonneg (norm_nonneg (![v 1, v 2] : Fin 2 → ℝ))
    (norm_nonneg (![w 1, w 2] : Fin 2 → ℝ))]

theorem stableCubicFirstBudget_norm {Y a : StableState} {b : ℝ}
    (hb1 : b ≤ 1) (hY : |Y 1| + |Y 2| ≤ b) :
    stableCubicFirstBudget Y a ≤ 4 * b ^ 2 * ‖a‖ := by
  have h2 := pow_le_pow_left₀ (by positivity : 0 ≤ |Y 1| + |Y 2|) hY 2
  have h3 := pow_le_pow_left₀ (by positivity : 0 ≤ |Y 1| + |Y 2|) hY 3
  have H0 := mul_le_mul_of_nonneg_right h3 (norm_nonneg a)
  have H1 := mul_le_mul h2 (stableTangent_split_bounds a).2.2 (norm_nonneg _) (sq_nonneg b)
  have H2 := mul_le_mul_of_nonneg_right hb1 (show 0 ≤ b ^ 2 * ‖a‖ by positivity)
  unfold stableCubicFirstBudget
  nlinarith only [H0, H1, H2]

theorem stableCubicFirstBudget_weighted {Y a v : StableState} {b E : ℝ}
    (hb : 0 ≤ b) (hE : 0 ≤ E) (hY : |Y 1| + |Y 2| ≤ b)
    (ha : ‖a‖ ≤ E * ‖v‖) (haz : ‖![a 1, a 2]‖ ≤ 256 * E * stableFirstInputWeight b v) :
    stableCubicFirstBudget Y a ≤ 769 * E * b ^ 2 * stableFirstInputWeight b v := by
  have h2 := pow_le_pow_left₀ (by positivity : 0 ≤ |Y 1| + |Y 2|) hY 2
  have h3 := pow_le_pow_left₀ (by positivity : 0 ≤ |Y 1| + |Y 2|) hY 3
  have H0 := mul_le_mul h3 ha (norm_nonneg _) (by positivity : 0 ≤ b ^ 3)
  have H1 := mul_le_mul h2 haz (norm_nonneg _) (sq_nonneg b)
  have hA : b * ‖v‖ ≤ stableFirstInputWeight b v := by
    unfold stableFirstInputWeight; exact le_add_of_nonneg_right (norm_nonneg _)
  have H2 := mul_le_mul_of_nonneg_left hA (show 0 ≤ E * b ^ 2 by positivity)
  unfold stableCubicFirstBudget
  nlinarith only [H0, H1, H2]

theorem stableCubicSecondBudget_weighted {Y a d v w : StableState} {b E : ℝ}
    (hb : 0 ≤ b) (hE : 0 ≤ E) (hY : |Y 1| + |Y 2| ≤ b)
    (ha : ‖a‖ ≤ E * ‖v‖) (hd : ‖d‖ ≤ E * ‖w‖)
    (haz : ‖![a 1, a 2]‖ ≤ 256 * E * stableFirstInputWeight b v)
    (hdz : ‖![d 1, d 2]‖ ≤ 256 * E * stableFirstInputWeight b w) :
    stableCubicSecondBudget Y a d ≤
      400000 * E ^ 2 * b * stableFirstInputWeight b v * stableFirstInputWeight b w := by
  let A := stableFirstInputWeight b v
  let B := stableFirstInputWeight b w
  have hA : 0 ≤ A := stableFirstInputWeight_nonneg hb v
  have hB : 0 ≤ B := stableFirstInputWeight_nonneg hb w
  have hav : b * ‖v‖ ≤ A := by dsimp [A, stableFirstInputWeight]; exact le_add_of_nonneg_right (norm_nonneg _)
  have hbw : b * ‖w‖ ≤ B := by dsimp [B, stableFirstInputWeight]; exact le_add_of_nonneg_right (norm_nonneg _)
  have h2 := pow_le_pow_left₀ (by positivity : 0 ≤ |Y 1| + |Y 2|) hY 2
  have h3 := pow_le_pow_left₀ (by positivity : 0 ≤ |Y 1| + |Y 2|) hY 3
  have H0 := mul_le_mul (mul_le_mul h3 ha (norm_nonneg _) (by positivity : 0 ≤ b ^ 3)) hd
    (norm_nonneg _) (by positivity : 0 ≤ b ^ 3 * (E * ‖v‖))
  have H1 := mul_le_mul h2 (mul_le_mul ha hdz (norm_nonneg _) (by positivity : 0 ≤ E * ‖v‖))
    (by positivity) (sq_nonneg b)
  have H2 := mul_le_mul h2 (mul_le_mul haz hd (norm_nonneg _) (by positivity : 0 ≤ 256 * E * A))
    (by positivity) (sq_nonneg b)
  have H3 := mul_le_mul (mul_le_mul hY haz (norm_nonneg _) hb) hdz
    (norm_nonneg _) (by positivity : 0 ≤ b * (256 * E * A))
  have T0 := mul_le_mul_of_nonneg_left (mul_le_mul hav hbw (by positivity) hA)
    (show 0 ≤ E ^ 2 * b by positivity)
  have T1 := mul_le_mul_of_nonneg_left hav (show 0 ≤ E ^ 2 * b * B by positivity)
  have T2 := mul_le_mul_of_nonneg_left hbw (show 0 ≤ E ^ 2 * b * A by positivity)
  change stableCubicSecondBudget Y a d ≤ 400000 * E ^ 2 * b * A * B
  dsimp only [A, B] at H0 H1 H2 H3 T0 T1 T2 ⊢
  unfold stableCubicSecondBudget
  nlinarith only [H0, H1, H2, H3, T0, T1, T2,
    show 0 ≤ E ^ 2 * b * stableFirstInputWeight b v * stableFirstInputWeight b w from
      mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg E) hb) hA) hB]

end BianchiIX
