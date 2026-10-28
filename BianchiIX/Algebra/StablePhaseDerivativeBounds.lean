import BianchiIX.Algebra.StablePhaseJetBounds

noncomputable section

namespace BianchiIX

theorem stableCorrectedPhase_directional_bounds {y : Fin 3 → ℝ} (hm : 2 ≤ y 0) :
    let b := |y 1| + |y 2|
    let L := y 0 + 1
    let P := fun z : Fin 3 → ℝ => stableCorrectedPhase (z 0) (z 1) (z 2)
    (∀ v, v 1 = 0 → v 2 = 0 → |fderiv ℝ P y v - v 0| ≤ 8 / L ^ 2 * b ^ 2 * ‖v‖) ∧
    (∀ v, v 0 = 0 → |fderiv ℝ P y v| ≤ 9 / L * b * ‖v‖) ∧
    (∀ v r, v 1 = 0 → v 2 = 0 → r 1 = 0 → r 2 = 0 →
      |fderiv ℝ (fderiv ℝ P) y v r| ≤ 33 / L ^ 3 * b ^ 2 * ‖v‖ * ‖r‖) ∧
    (∀ v r, v 1 = 0 → v 2 = 0 → r 0 = 0 →
      |fderiv ℝ (fderiv ℝ P) y v r| ≤ 15 / L ^ 2 * b * ‖v‖ * ‖r‖) ∧
    (∀ v r, v 0 = 0 → r 0 = 0 →
      |fderiv ℝ (fderiv ℝ P) y v r| ≤ 9 / L * ‖v‖ * ‖r‖) := by
  have hm1 : 1 < y 0 := by linarith
  have hL : 0 < y 0 + 1 := by linarith
  obtain ⟨h0, h1, h2, h00, h01, h02⟩ := stableCorrectedPhase_coefficient_bounds (u := y 1) (w := y 2) hm
  obtain ⟨ha, _, _, hc, _, _⟩ := stableCorrection_coefficients_bounds hm
  have h22 := (stableWeakRadius_coefficient_bounds (m := y 0) (w := y 2) (by linarith)).2.2.2.2
  have hv (v : Fin 3 → ℝ) (i : Fin 3) : |v i| ≤ ‖v‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm v i
  have hmul {a B : ℝ} (h : |a| ≤ B) (v : Fin 3 → ℝ) (i : Fin 3) :
      |a * v i| ≤ B * ‖v‖ := by
    rw [abs_mul]
    exact mul_le_mul h (hv v i) (abs_nonneg _) ((abs_nonneg a).trans h)
  have hprod {a B : ℝ} (h : |a| ≤ B) (v r : Fin 3 → ℝ) (i j : Fin 3) :
      |a * v i * r j| ≤ B * ‖v‖ * ‖r‖ := by
    have hB : 0 ≤ B := (abs_nonneg a).trans h
    rw [abs_mul]
    exact mul_le_mul (hmul h v i) (hv r j) (abs_nonneg _) (by positivity)
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro v hv1 hv2
    rw [stableCorrectedPhase_fderiv hm1]
    simp only [hv1, hv2, mul_zero, add_zero]
    rw [show stableCorrectedGradient (y 0) (y 1) (y 2) 0 * v 0 - v 0 =
      (stableCorrectedGradient (y 0) (y 1) (y 2) 0 - 1) * v 0 by ring]
    exact hmul h0 v 0
  · intro v hv0
    rw [stableCorrectedPhase_fderiv hm1]
    simp only [hv0, mul_zero, zero_add]
    have H := abs_add_le (stableCorrectedGradient (y 0) (y 1) (y 2) 1 * v 1)
      (stableCorrectedGradient (y 0) (y 1) (y 2) 2 * v 2)
    have H1 := hmul h1 v 1
    have H2 := hmul h2 v 2
    simp only [div_eq_mul_inv] at H1 H2 ⊢
    nlinarith only [H, H1, H2]
  · intro v r hv1 hv2 hr1 hr2
    rw [stableCorrectedPhase_fderiv2 hm1]
    simp only [stableCorrectedHessian, hv1, hv2, hr1, hr2, mul_zero, zero_mul, add_zero]
    exact hprod h00 v r 0 0
  · intro v r hv1 hv2 hr0
    rw [stableCorrectedPhase_fderiv2 hm1]
    simp only [stableCorrectedHessian, hv1, hv2, hr0, mul_zero, zero_mul, add_zero, zero_add, ← mul_assoc]
    have H1 := hprod h01 v r 0 1
    have H2 := hprod h02 v r 0 2
    have H := abs_add_le
      ((2 * stableCorrectionADeriv (y 0) * y 1 + stableCorrectionCDeriv (y 0) * y 2) * v 0 * r 1)
      ((-(y 0 + 1) * y 2 / stableWeakRadius (y 0) (y 2) ^ 3 + stableCorrectionCDeriv (y 0) * y 1) * v 0 * r 2)
    simp only [div_eq_mul_inv] at H H1 H2 ⊢
    nlinarith only [H, H1, H2]
  · intro v r hv0 hr0
    rw [stableCorrectedPhase_fderiv2 hm1]
    simp only [stableCorrectedHessian, hv0, hr0, mul_zero, zero_mul, add_zero, zero_add, mul_add, ← mul_assoc]
    have ha2 : |2 * stableCorrectionA (y 0)| ≤ 4 / (y 0 + 1) := by
      norm_num [abs_mul]
      simp only [div_eq_mul_inv] at ha ⊢
      linarith only [ha]
    have H1 := hprod ha2 v r 1 1
    have H2 := hprod hc.le v r 1 2
    have H3 := hprod hc.le v r 2 1
    have H4 := hprod h22 v r 2 2
    have htri (a b c d : ℝ) : |a + (b + c) + d| ≤ |a| + |b| + |c| + |d| := by
      linarith only [abs_add_le a (b + c), abs_add_le b c, abs_add_le (a + (b + c)) d]
    have H := htri (2 * stableCorrectionA (y 0) * v 1 * r 1)
      (stableCorrectionC (y 0) * v 1 * r 2) (stableCorrectionC (y 0) * v 2 * r 1)
      ((y 0 + 1) ^ 2 / stableWeakRadius (y 0) (y 2) ^ 3 * v 2 * r 2)
    simp only [div_eq_mul_inv] at H H1 H2 H3 H4 ⊢
    nlinarith only [H, H1, H2, H3, H4]

end BianchiIX
