import BianchiIX.Algebra.StableCubicMonomials

noncomputable section

namespace BianchiIX

theorem stableCubicMonomial_bound (i : Fin 4) (y : StableState) :
    |stableCubicMonomial i y| ≤ (|y 1| + |y 2|) ^ 3 := by
  let b := |y 1| + |y 2|
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hu : |y 1| ≤ b := by dsimp [b]; linarith [abs_nonneg (y 2)]
  have hw : |y 2| ≤ b := by dsimp [b]; linarith [abs_nonneg (y 1)]
  have hu2 := pow_le_pow_left₀ (abs_nonneg (y 1)) hu 2
  have hw2 := pow_le_pow_left₀ (abs_nonneg (y 2)) hw 2
  fin_cases i
  · exact (abs_pow (y 1) 3).le.trans (pow_le_pow_left₀ (abs_nonneg (y 1)) hu 3)
  · change |y 1 ^ 2 * y 2| ≤ b ^ 3
    rw [abs_mul, abs_pow]
    nlinarith only [mul_le_mul hu2 hw (abs_nonneg _) (sq_nonneg b)]
  · change |y 1 * y 2 ^ 2| ≤ b ^ 3
    rw [abs_mul, abs_pow]
    nlinarith only [mul_le_mul hu hw2 (sq_nonneg _) hb]
  · exact (abs_pow (y 2) 3).le.trans (pow_le_pow_left₀ (abs_nonneg (y 2)) hw 3)

theorem stableCubicMonomial_first_bound (i : Fin 4) (y v : StableState) :
    |fderiv ℝ (stableCubicMonomial i) y v| ≤ 3 * (|y 1| + |y 2|) ^ 2 * ‖![v 1, v 2]‖ := by
  let b := |y 1| + |y 2|
  let V := ‖![v 1, v 2]‖
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hu : |y 1| ≤ b := by dsimp [b]; linarith [abs_nonneg (y 2)]
  have hw : |y 2| ≤ b := by dsimp [b]; linarith [abs_nonneg (y 1)]
  have hv1 : |v 1| ≤ V := by simpa only [Real.norm_eq_abs, Matrix.cons_val_zero] using norm_le_pi_norm ![v 1, v 2] 0
  have hv2 : |v 2| ≤ V := by simpa only [Real.norm_eq_abs, Matrix.cons_val_one, Matrix.cons_val_zero] using norm_le_pi_norm ![v 1, v 2] 1
  have hp (p q r : ℝ) (hp : |p| ≤ b) (hq : |q| ≤ b) (hr : |r| ≤ V) :
      |p| * |q| * |r| ≤ b ^ 2 * V := by
    have H := mul_le_mul (mul_le_mul hp hq (abs_nonneg _) hb) hr (abs_nonneg _) (mul_nonneg hb hb)
    nlinarith only [H]
  have H11 := hp (y 1) (y 1) (v 1) hu hu hv1
  have H12 := hp (y 1) (y 2) (v 1) hu hw hv1
  have H13 := hp (y 1) (y 1) (v 2) hu hu hv2
  have H21 := hp (y 2) (y 2) (v 1) hw hw hv1
  have H22 := hp (y 1) (y 2) (v 2) hu hw hv2
  have H23 := hp (y 2) (y 2) (v 2) hw hw hv2
  rw [stableCubicMonomial_fderiv]
  fin_cases i
  · change |3 * y 1 ^ 2 * v 1| ≤ _
    simp only [abs_mul, abs_pow]
    norm_num only
    nlinarith only [H11]
  · have H := abs_add_le (2 * y 1 * y 2 * v 1) (y 1 ^ 2 * v 2)
    change |2 * y 1 * y 2 * v 1 + y 1 ^ 2 * v 2| ≤ _
    simp only [abs_mul, abs_pow] at H
    norm_num only at H
    nlinarith only [H, H12, H13]
  · have H := abs_add_le (y 2 ^ 2 * v 1) (2 * y 1 * y 2 * v 2)
    change |y 2 ^ 2 * v 1 + 2 * y 1 * y 2 * v 2| ≤ _
    simp only [abs_mul, abs_pow] at H
    norm_num only at H
    nlinarith only [H, H21, H22]
  · change |3 * y 2 ^ 2 * v 2| ≤ _
    simp only [abs_mul, abs_pow]
    norm_num only
    nlinarith only [H23]

theorem stableCubicMonomial_second_bound (i : Fin 4) (y v w : StableState) :
    |fderiv ℝ (fderiv ℝ (stableCubicMonomial i)) y v w| ≤
      6 * (|y 1| + |y 2|) * ‖![v 1, v 2]‖ * ‖![w 1, w 2]‖ := by
  let b := |y 1| + |y 2|
  let V := ‖![v 1, v 2]‖
  let W := ‖![w 1, w 2]‖
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hV : 0 ≤ V := norm_nonneg _
  have hu : |y 1| ≤ b := by dsimp [b]; linarith [abs_nonneg (y 2)]
  have hw : |y 2| ≤ b := by dsimp [b]; linarith [abs_nonneg (y 1)]
  have hz (a : StableState) : |a 1| ≤ ‖![a 1, a 2]‖ ∧ |a 2| ≤ ‖![a 1, a 2]‖ := by
    constructor
    · simpa only [Real.norm_eq_abs, Matrix.cons_val_zero] using norm_le_pi_norm ![a 1, a 2] 0
    · simpa only [Real.norm_eq_abs, Matrix.cons_val_one, Matrix.cons_val_zero] using norm_le_pi_norm ![a 1, a 2] 1
  have hp (p q r : ℝ) (hp : |p| ≤ b) (hq : |q| ≤ V) (hr : |r| ≤ W) :
      |p| * |q| * |r| ≤ b * V * W :=
    mul_le_mul (mul_le_mul hp hq (abs_nonneg _) hb) hr (abs_nonneg _) (mul_nonneg hb hV)
  have H111 := hp (y 1) (v 1) (w 1) hu (hz v).1 (hz w).1
  have H211 := hp (y 2) (v 1) (w 1) hw (hz v).1 (hz w).1
  have H112 := hp (y 1) (v 1) (w 2) hu (hz v).1 (hz w).2
  have H121 := hp (y 1) (v 2) (w 1) hu (hz v).2 (hz w).1
  have H212 := hp (y 2) (v 1) (w 2) hw (hz v).1 (hz w).2
  have H221 := hp (y 2) (v 2) (w 1) hw (hz v).2 (hz w).1
  have H122 := hp (y 1) (v 2) (w 2) hu (hz v).2 (hz w).2
  have H222 := hp (y 2) (v 2) (w 2) hw (hz v).2 (hz w).2
  have htri (a b c : ℝ) : |a + b + c| ≤ |a| + |b| + |c| := by
    linarith only [abs_add_le a b, abs_add_le (a + b) c]
  rw [stableCubicMonomial_fderiv2]
  fin_cases i
  · change |6 * y 1 * v 1 * w 1| ≤ _
    simp only [abs_mul]
    norm_num only
    nlinarith only [H111]
  · have H := htri (2 * y 2 * v 1 * w 1) (2 * y 1 * v 1 * w 2) (2 * y 1 * v 2 * w 1)
    change |2 * y 2 * v 1 * w 1 + 2 * y 1 * v 1 * w 2 + 2 * y 1 * v 2 * w 1| ≤ _
    simp only [abs_mul] at H
    norm_num only at H
    nlinarith only [H, H211, H112, H121]
  · have H := htri (2 * y 2 * v 1 * w 2) (2 * y 2 * v 2 * w 1) (2 * y 1 * v 2 * w 2)
    change |2 * y 2 * v 1 * w 2 + 2 * y 2 * v 2 * w 1 + 2 * y 1 * v 2 * w 2| ≤ _
    simp only [abs_mul] at H
    norm_num only at H
    nlinarith only [H, H212, H221, H122]
  · change |6 * y 2 * v 2 * w 2| ≤ _
    simp only [abs_mul]
    norm_num only
    nlinarith only [H222]

end BianchiIX
