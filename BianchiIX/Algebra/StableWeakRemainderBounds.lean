import BianchiIX.Algebra.StableWeakRemainderFactorization

noncomputable section

namespace BianchiIX

theorem stableWeakRemainder_coefficient_bounds {m w : ℝ} (hm : -1 < m) :
    |stableWeakRemainder m w| ≤ w ^ 4 / (m + 1) ^ 3 ∧
      |stableWeakRemainderM m w| ≤ w ^ 4 / (m + 1) ^ 4 ∧
      |stableWeakRemainderW m w| ≤ |w| ^ 3 / (m + 1) ^ 3 ∧
      |stableWeakRemainderMM m w| ≤ 3 * w ^ 4 / (m + 1) ^ 5 ∧
      |stableWeakRemainderMW m w| ≤ 3 * |w| ^ 3 / (m + 1) ^ 4 ∧
      |stableWeakRemainderWW m w| ≤ 3 * w ^ 2 / (m + 1) ^ 3 := by
  have hL : 0 < m + 1 := by linarith
  have hS := stableWeakRadius_pos (w := w) hm
  have hsum : 0 < stableWeakRadius m w + (m + 1) := by positivity
  have hLS : m + 1 ≤ stableWeakRadius m w := phaseNorm_ge hL.le
  have hsumL : m + 1 ≤ stableWeakRadius m w + (m + 1) := by linarith
  have hden : (m + 1) ^ 2 ≤ stableWeakRadius m w * (stableWeakRadius m w + (m + 1)) := by
    nlinarith only [mul_le_mul hLS hsumL hL.le hS.le]
  obtain ⟨hM, hW⟩ := stableWeakRemainder_gradient_factorization (w := w) hm
  obtain ⟨hMM, hMW, hWW⟩ := stableWeakRemainder_hessian_factorization (w := w) hm
  obtain ⟨hK0, hK⟩ := stableWeakSecondKernel_bounds (w := w) hm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [stableWeakRemainder_factorization hm, abs_div, abs_neg,
      abs_of_nonneg (by positivity : 0 ≤ w ^ 4), abs_of_pos (by positivity)]
    apply div_le_div_of_nonneg_left (by positivity) (pow_pos hL 3)
    have H := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hL.le hsumL 2) hL.le
    nlinarith only [H, le_of_lt (pow_pos hL 3)]
  · rw [hM, abs_of_nonneg (by positivity)]
    calc
      _ ≤ w ^ 4 * (2 * (stableWeakRadius m w + (m + 1))) /
          (2 * (m + 1) ^ 2 * stableWeakRadius m w * (stableWeakRadius m w + (m + 1)) ^ 2) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left (by linarith : stableWeakRadius m w + 2 * (m + 1) ≤
          2 * (stableWeakRadius m w + (m + 1))) (by positivity)
      _ = w ^ 4 / ((m + 1) ^ 2 * (stableWeakRadius m w * (stableWeakRadius m w + (m + 1)))) := by field_simp
      _ ≤ w ^ 4 / (m + 1) ^ 4 := by
        apply div_le_div_of_nonneg_left (by positivity) (pow_pos hL 4)
        nlinarith only [mul_le_mul_of_nonneg_left hden (sq_nonneg (m + 1))]
  · rw [hW, abs_div, abs_neg, abs_pow, abs_of_pos (show 0 <
      (m + 1) * stableWeakRadius m w * (stableWeakRadius m w + (m + 1)) by positivity)]
    apply div_le_div_of_nonneg_left (by positivity) (pow_pos hL 3)
    nlinarith only [mul_le_mul_of_nonneg_left hden hL.le]
  · rw [hMM, abs_mul, abs_neg, abs_of_nonneg (by positivity), abs_of_nonneg hK0]
    calc
      _ ≤ (w ^ 4 / (m + 1) ^ 3) * (3 / (m + 1) ^ 2) :=
        mul_le_mul_of_nonneg_left hK (by positivity)
      _ = 3 * w ^ 4 / (m + 1) ^ 5 := by field_simp
  · rw [hMW, abs_mul, abs_div, abs_pow, abs_of_pos (pow_pos hL 2), abs_of_nonneg hK0]
    calc
      _ ≤ (|w| ^ 3 / (m + 1) ^ 2) * (3 / (m + 1) ^ 2) :=
        mul_le_mul_of_nonneg_left hK (by positivity)
      _ = 3 * |w| ^ 3 / (m + 1) ^ 4 := by field_simp
  · rw [hWW, abs_mul, abs_neg, abs_of_nonneg (by positivity), abs_of_nonneg hK0]
    calc
      _ ≤ (w ^ 2 / (m + 1)) * (3 / (m + 1) ^ 2) :=
        mul_le_mul_of_nonneg_left hK (by positivity)
      _ = 3 * w ^ 2 / (m + 1) ^ 3 := by field_simp

theorem stableWeakRemainder_directional_bounds {y : Fin 3 → ℝ} (hm : -1 < y 0) :
    let b := |y 1| + |y 2|
    let L := y 0 + 1
    let E := fun z : Fin 3 → ℝ => stableWeakRemainder (z 0) (z 2)
    |E y| ≤ b ^ 4 / L ^ 3 ∧
    (∀ v, v 1 = 0 → v 2 = 0 → |fderiv ℝ E y v| ≤ b ^ 4 / L ^ 4 * ‖v‖) ∧
    (∀ v, v 0 = 0 → |fderiv ℝ E y v| ≤ b ^ 3 / L ^ 3 * ‖v‖) ∧
    (∀ v r, v 1 = 0 → v 2 = 0 → r 1 = 0 → r 2 = 0 →
      |fderiv ℝ (fderiv ℝ E) y v r| ≤ 3 * b ^ 4 / L ^ 5 * ‖v‖ * ‖r‖) ∧
    (∀ v r, v 1 = 0 → v 2 = 0 → r 0 = 0 →
      |fderiv ℝ (fderiv ℝ E) y v r| ≤ 3 * b ^ 3 / L ^ 4 * ‖v‖ * ‖r‖) ∧
    (∀ v r, v 0 = 0 → r 0 = 0 →
      |fderiv ℝ (fderiv ℝ E) y v r| ≤ 3 * b ^ 2 / L ^ 3 * ‖v‖ * ‖r‖) := by
  let b := |y 1| + |y 2|
  have hL : 0 < y 0 + 1 := by linarith
  have hw : |y 2| ≤ b := le_add_of_nonneg_left (abs_nonneg (y 1))
  have hw2 : y 2 ^ 2 ≤ b ^ 2 := by simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hw 2
  have hw3 := pow_le_pow_left₀ (abs_nonneg (y 2)) hw 3
  have hw4 : y 2 ^ 4 ≤ b ^ 4 := by
    have H := pow_le_pow_left₀ (abs_nonneg (y 2)) hw 4
    rw [← abs_pow] at H
    exact (le_abs_self _).trans H
  obtain ⟨h0, hM, hW, hMM, hMW, hWW⟩ := stableWeakRemainder_coefficient_bounds (w := y 2) hm
  have hM' := hM.trans (div_le_div_of_nonneg_right hw4 (show 0 ≤ (y 0 + 1) ^ 4 by positivity))
  have hW' := hW.trans (div_le_div_of_nonneg_right hw3 (show 0 ≤ (y 0 + 1) ^ 3 by positivity))
  have hMM' := hMM.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hw4 (by norm_num : (0 : ℝ) ≤ 3)) (show 0 ≤ (y 0 + 1) ^ 5 by positivity))
  have hMW' := hMW.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hw3 (by norm_num : (0 : ℝ) ≤ 3)) (show 0 ≤ (y 0 + 1) ^ 4 by positivity))
  have hWW' := hWW.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hw2 (by norm_num : (0 : ℝ) ≤ 3)) (show 0 ≤ (y 0 + 1) ^ 3 by positivity))
  have hv (v : Fin 3 → ℝ) (i : Fin 3) : |v i| ≤ ‖v‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm v i
  have hmul {a B : ℝ} (h : |a| ≤ B) (v : Fin 3 → ℝ) (i : Fin 3) : |a * v i| ≤ B * ‖v‖ := by
    rw [abs_mul]
    exact mul_le_mul h (hv v i) (abs_nonneg _) ((abs_nonneg a).trans h)
  have hprod {a B : ℝ} (h : |a| ≤ B) (v r : Fin 3 → ℝ) (i j : Fin 3) : |a * v i * r j| ≤ B * ‖v‖ * ‖r‖ := by
    have hB : 0 ≤ B := (abs_nonneg a).trans h
    rw [abs_mul]
    exact mul_le_mul (hmul h v i) (hv r j) (abs_nonneg _) (by positivity)
  dsimp only
  refine ⟨h0.trans (div_le_div_of_nonneg_right hw4 (by positivity)), ?_, ?_, ?_, ?_, ?_⟩
  · intro v _ hv2
    rw [stableWeakRemainder_fderiv hm, hv2, mul_zero, add_zero]
    exact hmul hM' v 0
  · intro v hv0
    rw [stableWeakRemainder_fderiv hm, hv0, mul_zero, zero_add]
    exact hmul hW' v 2
  · intro v r _ hv2 _ hr2
    rw [stableWeakRemainder_fderiv2 hm]
    simp only [hv2, hr2, mul_zero, zero_mul, add_zero]
    exact hprod hMM' v r 0 0
  · intro v r _ hv2 hr0
    rw [stableWeakRemainder_fderiv2 hm]
    simp only [hv2, hr0, mul_zero, zero_mul, add_zero, zero_add, ← mul_assoc]
    exact hprod hMW' v r 0 2
  · intro v r hv0 hr0
    rw [stableWeakRemainder_fderiv2 hm]
    simp only [hv0, hr0, mul_zero, zero_mul, add_zero, zero_add]
    exact hprod hWW' v r 2 2

end BianchiIX
