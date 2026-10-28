import BianchiIX.Analysis.ConnectionFeedbackBounds

noncomputable section

namespace BianchiIX

theorem connectionTransverseMatrix_strong_forcing {μ : ℝ} {y : ProjectiveState} (hμ : 4 ≤ μ)
    (hm : |-y 0 - μ| ≤ 1 / 2) (hu : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000)
    (hv : 0 ≤ y 2 ∧ y 2 ≤ 1) (hw : 0 ≤ y 3 ∧ y 3 ≤ 1) (x : ℝ) :
    ‖(connectionTransverseMatrix μ (-y 0) (y 1) (y 2) (y 3)).mulVec ![x, 0]‖ ≤
      64 * μ * y 1 * |x| := by
  have hμ0 : 0 < μ := by linarith only [hμ]
  apply (pi_norm_le_iff_of_nonempty _).mpr
  intro i
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  fin_cases i
  · change ‖connectionStrongClockPartials (-y 0) (y 1) (y 2) (y 3) 1 * x + _ * 0‖ ≤ _
    rw [mul_zero, add_zero, Real.norm_eq_abs, abs_mul]
    apply (mul_le_mul_of_nonneg_right (connectionStrongClockPartials_bounds hμ hm hu hv hw).2.1 (abs_nonneg x)).trans
    exact mul_le_mul_of_nonneg_right
      (by nlinarith only [mul_le_mul_of_nonneg_right hμ hu.1, hu.1]) (abs_nonneg x)
  · change ‖(μ ^ 2 * connectionWeakClockPartials (-y 0) (y 1) (y 2) (y 3) 1) * x + _ * 0‖ ≤ _
    rw [mul_zero, add_zero, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg μ)]
    apply (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (connectionWeakClockPartials_bounds hμ hm hu hv hw).2.1 (sq_nonneg μ))
      (abs_nonneg x)).trans_eq
    field_simp

/-- Retaining the strong column separately prevents the entry factor 1/u from entering feedback. -/
theorem connectionPhase_shifted_variation_bound {μ : ℝ} {y : ProjectiveState} (hμ : 4 ≤ μ)
    (hm : |-y 0 - μ| ≤ 1 / 2) (hu : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000)
    (hv : 0 ≤ y 2 ∧ y 2 ≤ 1) (hw : 0 ≤ y 3 ∧ y 3 ≤ 1)
    (d : Fin 4 → ℝ) (hz : d 3 = 0) (x : ℝ) :
    |connectionLogLinearizedRates y d 0| ≤ 32 * y 1 * |x| +
      64 * (y 1 / μ ^ 2 + (y 2 * y 3) ^ 2 / μ ^ 4) * |d 0| +
      64 * (y 1 + (y 2 * y 3) ^ 2 / μ ^ 5) * ‖connectionWeightedTangent μ d - ![x, 0]‖ := by
  let r : Fin 4 → ℝ := ![d 0, d 1 - x, d 2, 0]
  have hr : r 3 = 0 := rfl
  have hweighted : connectionWeightedTangent μ r = connectionWeightedTangent μ d - ![x, 0] := by
    ext i
    fin_cases i <;> simp [connectionWeightedTangent, r]
  have hid : connectionLogLinearizedRates y d 0 = connectionLogLinearizedRates y r 0 +
      connectionPhaseGPartials (-y 0) (y 1) (y 2) (y 3) 1 * x := by
    change (∑ j : Fin 4, connectionPhaseGPartials (-y 0) (y 1) (y 2) (y 3) j * d j) =
      (∑ j : Fin 4, connectionPhaseGPartials (-y 0) (y 1) (y 2) (y 3) j * r j) + _
    simp [Fin.sum_univ_succ, r, hz]
    ring
  have H := connectionPhase_variation_bound hμ hm hu hv hw r hr
  rw [hweighted] at H
  rw [hid]
  have Hx := mul_le_mul_of_nonneg_right (connectionPhaseGPartials_bounds hμ hm hu hv hw).2.1 (abs_nonneg x)
  exact (abs_add_le _ _).trans ((add_le_add H (by simpa only [abs_mul] using Hx)).trans_eq (by dsimp [r]; ring))

def connectionStrongSource (μ u₀ u p x : ℝ) : ℝ :=
  |x| * (32 * u + 16384 * u₀ * (u + p ^ 2 / μ ^ 5))

def connectionStrongSourceBudget (μ u p x : ℝ) : ℝ :=
  |x| * (64 * u / μ + 32768 * u ^ 2 / μ + 4096 * u * p ^ 2 / μ ^ 4)

theorem connectionStrongSource_nonneg {μ u₀ u p x : ℝ}
    (hμ : 0 ≤ μ) (hu₀ : 0 ≤ u₀) (hu : 0 ≤ u) :
    0 ≤ connectionStrongSource μ u₀ u p x := by
  unfold connectionStrongSource
  positivity

theorem connectionStrongSourceBudget_ordinary {μ u p : ℝ} (hμ : 4 ≤ μ)
    (hu : 0 < u ∧ u ≤ (1 / 10000) / μ) (hp : 0 ≤ p ∧ p ≤ 1 / 10000) :
    connectionStrongSourceBudget μ u p (1 / u) ≤ 65 / μ := by
  have hμ0 : 0 < μ := by linarith only [hμ]
  have hμ2 : 16 ≤ μ ^ 2 := by nlinarith only [hμ, sq_nonneg (μ - 4)]
  have hμ3 : 64 ≤ μ ^ 3 := by nlinarith only [mul_le_mul_of_nonneg_right hμ2 hμ0.le, hμ]
  have hu' : u ≤ 1 / 40000 := hu.2.trans
    ((div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1 / 10000) (by norm_num : (0 : ℝ) < 4) hμ).trans_eq (by norm_num))
  have hp2 : p ^ 2 ≤ 1 / 100000000 := by nlinarith only [hp.1, hp.2, mul_nonneg hp.1 (sub_nonneg.mpr hp.2)]
  have hp3 : p ^ 2 / μ ^ 3 ≤ 1 / 6400000000 :=
    (div_le_div_of_nonneg_right hp2 (by positivity)).trans
      ((div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1 / 100000000) (by norm_num : (0 : ℝ) < 64) hμ3).trans_eq (by norm_num))
  have hid : connectionStrongSourceBudget μ u p (1 / u) =
      (64 + 32768 * u + 4096 * (p ^ 2 / μ ^ 3)) / μ := by
    unfold connectionStrongSourceBudget
    rw [abs_of_pos (one_div_pos.mpr hu.1)]
    field_simp [ne_of_gt hu.1]
  rw [hid]
  exact div_le_div_of_nonneg_right (by linarith only [hu', hp3]) hμ0.le

end BianchiIX
