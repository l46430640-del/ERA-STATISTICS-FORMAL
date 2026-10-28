import BianchiIX.Analysis.ConnectionWeightedVariation

noncomputable section

namespace BianchiIX

def connectionPhaseFeedbackRate (μ τ u p : ℝ) : ℝ :=
  64 * (u / μ ^ 2 + p ^ 2 / μ ^ 4) + 8192 * τ * (u + p ^ 2 / μ ^ 5)

def connectionPhaseFeedbackBudget (μ u p : ℝ) : ℝ :=
  64 * (2 * u / μ ^ 3 + p ^ 2 / (4 * μ ^ 3)) +
    8192 * (4 * u / μ ^ 2 + p ^ 2 / (16 * μ ^ 3))

theorem connectionPhaseFeedbackRate_nonneg {μ τ u p : ℝ} (hμ : 0 ≤ μ) (hτ : 0 ≤ τ) (hu : 0 ≤ u) :
    0 ≤ connectionPhaseFeedbackRate μ τ u p := by
  unfold connectionPhaseFeedbackRate
  positivity

theorem connectionPhaseFeedbackBudget_nonneg {μ u p : ℝ} (hμ : 0 ≤ μ) (hu : 0 ≤ u) :
    0 ≤ connectionPhaseFeedbackBudget μ u p := by
  unfold connectionPhaseFeedbackBudget
  positivity

theorem connectionPhaseFeedbackBudget_small {μ u p : ℝ} (hμ : 4 ≤ μ)
    (hu : 0 ≤ u ∧ u ≤ (1 / 10000) / μ) (hp : 0 ≤ p ∧ p ≤ 1 / 10000) :
    connectionPhaseFeedbackBudget μ u p ≤ 1 / 16 := by
  have hμ0 : 0 < μ := by linarith only [hμ]
  have hμ2 : 16 ≤ μ ^ 2 := by nlinarith only [hμ, sq_nonneg (μ - 4)]
  have hμ3 : 64 ≤ μ ^ 3 := by nlinarith only [mul_le_mul_of_nonneg_right hμ2 hμ0.le, hμ]
  have hu' : u ≤ 1 / 40000 := hu.2.trans
    ((div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1 / 10000) (by norm_num : (0 : ℝ) < 4) hμ).trans_eq (by norm_num))
  have hp2 : p ^ 2 ≤ 1 / 100000000 := by nlinarith only [hp.1, hp.2, mul_nonneg hp.1 (sub_nonneg.mpr hp.2)]
  have H1 : u / μ ^ 3 ≤ 1 / 2560000 :=
    (div_le_div_of_nonneg_right hu' (by positivity)).trans
      ((div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1 / 40000) (by norm_num : (0 : ℝ) < 64) hμ3).trans_eq (by norm_num))
  have H2 : u / μ ^ 2 ≤ 1 / 640000 :=
    (div_le_div_of_nonneg_right hu' (by positivity)).trans
      ((div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1 / 40000) (by norm_num : (0 : ℝ) < 16) hμ2).trans_eq (by norm_num))
  have H3 : p ^ 2 / μ ^ 3 ≤ 1 / 6400000000 :=
    (div_le_div_of_nonneg_right hp2 (by positivity)).trans
      ((div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1 / 100000000) (by norm_num : (0 : ℝ) < 64) hμ3).trans_eq (by norm_num))
  have hid : connectionPhaseFeedbackBudget μ u p = 128 * (u / μ ^ 3) +
      32768 * (u / μ ^ 2) + 528 * (p ^ 2 / μ ^ 3) := by unfold connectionPhaseFeedbackBudget; ring
  rw [hid]
  linarith only [H1, H2, H3]

theorem connectionPhase_transverse_row_bound {μ : ℝ} {y : ProjectiveState} (hμ : 4 ≤ μ)
    (hm : |-y 0 - μ| ≤ 1 / 2) (hu : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000)
    (hv : 0 ≤ y 2 ∧ y 2 ≤ 1) (hw : 0 ≤ y 3 ∧ y 3 ≤ 1) :
    |connectionPhaseGPartials (-y 0) (y 1) (y 2) (y 3) 1| +
      |connectionPhaseGPartials (-y 0) (y 1) (y 2) (y 3) 2| / μ ^ 2 ≤
        64 * (y 1 + (y 2 * y 3) ^ 2 / μ ^ 5) := by
  have hμ0 : 0 < μ := by linarith only [hμ]
  have hμ2 : 1 ≤ μ ^ 2 := by nlinarith only [hμ, sq_nonneg (μ - 4)]
  have hG := connectionPhaseGPartials_bounds hμ hm hu hv hw
  have huv : y 1 * y 2 / μ ^ 2 ≤ y 1 := by
    apply (div_le_iff₀ (sq_pos_of_pos hμ0)).mpr
    exact (mul_le_mul_of_nonneg_left hv.2 hu.1).trans
      (by simpa using mul_le_mul_of_nonneg_left hμ2 hu.1)
  have H := add_le_add hG.2.1 (div_le_div_of_nonneg_right hG.2.2.1 (sq_nonneg μ))
  have hid : 32 * (y 1 * y 2 + (y 2 * y 3) ^ 2 / μ ^ 3) / μ ^ 2 =
      32 * (y 1 * y 2 / μ ^ 2) + 32 * ((y 2 * y 3) ^ 2 / μ ^ 5) := by field_simp
  rw [hid] at H
  have hp : 0 ≤ (y 2 * y 3) ^ 2 / μ ^ 5 := by positivity
  linarith only [H, huv, hp]

theorem connectionPhase_variation_bound {μ : ℝ} {y : ProjectiveState} (hμ : 4 ≤ μ)
    (hm : |-y 0 - μ| ≤ 1 / 2) (hu : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000)
    (hv : 0 ≤ y 2 ∧ y 2 ≤ 1) (hw : 0 ≤ y 3 ∧ y 3 ≤ 1) (d : Fin 4 → ℝ) (hz : d 3 = 0) :
    |connectionLogLinearizedRates y d 0| ≤
      64 * (y 1 / μ ^ 2 + (y 2 * y 3) ^ 2 / μ ^ 4) * |d 0| +
      64 * (y 1 + (y 2 * y 3) ^ 2 / μ ^ 5) * ‖connectionWeightedTangent μ d‖ := by
  let G := connectionPhaseGPartials (-y 0) (y 1) (y 2) (y 3)
  have hμ0 : 0 < μ := by linarith only [hμ]
  have hx : |d 1| ≤ ‖connectionWeightedTangent μ d‖ := by
    simpa [connectionWeightedTangent, Real.norm_eq_abs] using norm_le_pi_norm (connectionWeightedTangent μ d) 0
  have hy : |d 2| ≤ ‖connectionWeightedTangent μ d‖ / μ ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hμ0)).mpr
    have H := norm_le_pi_norm (connectionWeightedTangent μ d) 1
    simpa [connectionWeightedTangent, Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg μ), mul_comm] using H
  have hsum : |connectionLogLinearizedRates y d 0| ≤ |G 0| * |d 0| + |G 1| * |d 1| + |G 2| * |d 2| := by
    change |∑ j : Fin 4, G j * d j| ≤ _
    simpa [Fin.sum_univ_succ, abs_mul, hz, add_assoc] using
      (abs_add_le (G 0 * d 0) (G 1 * d 1 + G 2 * d 2)).trans
        (add_le_add (le_refl |G 0 * d 0|) (abs_add_le (G 1 * d 1) (G 2 * d 2)))
  have H := hsum.trans (add_le_add (add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hx (abs_nonneg _)))
    (mul_le_mul_of_nonneg_left hy (abs_nonneg _)))
  have hJ := (connectionPhaseGPartials_bounds hμ hm hu hv hw).1
  have hT := connectionPhase_transverse_row_bound hμ hm hu hv hw
  calc
    _ ≤ |G 0| * |d 0| + (|G 1| + |G 2| / μ ^ 2) * ‖connectionWeightedTangent μ d‖ := H.trans_eq (by ring)
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_right hJ (abs_nonneg _))
      (mul_le_mul_of_nonneg_right hT (norm_nonneg _))

end BianchiIX
