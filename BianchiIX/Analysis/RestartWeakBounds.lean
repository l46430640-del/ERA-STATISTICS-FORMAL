import BianchiIX.Analysis.RestartMixedBounds

noncomputable section

namespace BianchiIX

def restartCompactWeakRates (x : RestartState) : Fin 2 → ℝ :=
  ![restartCompactWeakRate 1 x, restartCompactWeakRate (-1) x]

def restartMixedWeakRates : RestartState → Fin 2 → ℝ := restartCompactWeakRates ∘ restartExpCoordinates

theorem contDiffAt_restartCompactWeakRates {x : RestartState} (hx : 0 < restartRadicand x)
    (k : WithTop ℕ∞) : ContDiffAt ℝ k restartCompactWeakRates x := by
  have hr := contDiffAt_restartCompactRoot hx k
  rw [contDiffAt_pi]
  intro i
  fin_cases i <;> dsimp [restartCompactWeakRates, restartCompactWeakRate, curvature] <;> fun_prop

theorem restartCompactWeakRates_zero : restartCompactWeakRates 0 = 0 := by
  ext i
  fin_cases i <;> norm_num [restartCompactWeakRates, restartCompactWeakRate,
    restartCompactRoot, restartRadicand, curvature]

theorem exists_restartCompactWeakRates_bounds :
    ∃ C ≥ (1 : ℝ), ∀ x : RestartState, ‖x‖ ≤ 1 / 16 →
      ‖restartCompactWeakRates x‖ ≤ C * ‖x‖ ∧
        ‖fderiv ℝ restartCompactWeakRates x‖ ≤ C ∧
        ‖fderiv ℝ (fderiv ℝ restartCompactWeakRates) x‖ ≤ C := by
  let S := Metric.closedBall (0 : RestartState) (1 / 16)
  have hreg (x : RestartState) (hx : x ∈ S) : ContDiffAt ℝ 3 restartCompactWeakRates x := by
    have H := (restartCompact_box_bounds (by simpa [S] using hx)).2.1
    exact contDiffAt_restartCompactWeakRates (by linarith only [H]) 3
  let q := fun x => ‖fderiv ℝ restartCompactWeakRates x‖ + ‖fderiv ℝ (fderiv ℝ restartCompactWeakRates) x‖
  have hq : ContinuousOn q S := by
    intro x hx
    have HD := (hreg x hx).fderiv_right (m := 2) (by norm_num)
    exact (HD.continuousAt.norm.add
      (HD.fderiv_right (m := 1) (by norm_num)).continuousAt.norm).continuousWithinAt
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : RestartState) (1 / 16)).exists_bound_of_continuousOn hq
  let C := max B 1
  have hbound (x : RestartState) (hx : x ∈ S) :
      ‖fderiv ℝ restartCompactWeakRates x‖ ≤ C ∧
        ‖fderiv ℝ (fderiv ℝ restartCompactWeakRates) x‖ ≤ C := by
    have H : q x ≤ C := (le_abs_self _).trans ((hB x hx).trans (le_max_left B 1))
    dsimp only [q] at H
    exact ⟨by linarith only [H, norm_nonneg (fderiv ℝ (fderiv ℝ restartCompactWeakRates) x)],
      by linarith only [H, norm_nonneg (fderiv ℝ restartCompactWeakRates x)]⟩
  refine ⟨C, le_max_right _ _, ?_⟩
  intro x hx
  have hxS : x ∈ S := by simpa [S] using hx
  have hzS : (0 : RestartState) ∈ S := by simp [S]
  have H := Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun z hz => (hreg z hz).differentiableAt (by norm_num))
    (fun z hz => (hbound z hz).1) (convex_closedBall (0 : RestartState) (1 / 16)) hzS hxS
  exact ⟨by simpa only [restartCompactWeakRates_zero, sub_zero] using H, hbound x hxS⟩

/-- A common constant supplies all fixed-domain bounds used in the nonlinear fast layer. -/
theorem exists_restartMixed_fastLayer_bounds :
    ∃ C ≥ (32 : ℝ), ∀ y : RestartState, ‖restartExpCoordinates y‖ ≤ 1 / 16 →
      ‖fderiv ℝ restartMixedField y‖ ≤ C * ‖restartExpCoordinates y‖ ∧
      ‖fderiv ℝ (fderiv ℝ restartMixedField) y‖ ≤ C ∧
      ‖restartMixedWeakRates y‖ ≤ C * ‖restartExpCoordinates y‖ ∧
      ‖fderiv ℝ restartMixedWeakRates y‖ ≤ C ∧
      ‖fderiv ℝ (fderiv ℝ restartMixedWeakRates) y‖ ≤ C ∧
      -4 < restartMixedField y 0 ∧ restartMixedField y 0 < -2 := by
  obtain ⟨A, _, HA⟩ := exists_restartMixed_derivative_bounds
  obtain ⟨B, hB, HB⟩ := exists_restartCompactWeakRates_bounds
  let C := max 32 (max A (2 * B))
  have hA : A ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have h2B : 2 * B ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  have hB0 : 0 ≤ B := by linarith only [hB]
  have hBC : B ≤ C := by linarith only [h2B, hB0]
  refine ⟨C, le_max_left _ _, ?_⟩
  intro y hy
  have hn : Real.exp (y 0) ≤ 1 := by
    have H : |Real.exp (y 0)| ≤ 1 / 16 := (norm_le_pi_norm (restartExpCoordinates y) 0).trans hy
    rw [abs_of_pos (Real.exp_pos _)] at H
    linarith only [H]
  have hbox := restartCompact_box_bounds hy
  have hr : 0 < restartRadicand (restartExpCoordinates y) := by linarith only [hbox.2.1]
  have H := composition_second_derivative_bounds (contDiff_restartExpCoordinates 2).contDiffAt
    (contDiffAt_restartCompactWeakRates hr 2) hB0 hB0 (by norm_num : (0 : ℝ) ≤ 1)
    (restartExpCoordinates_derivative_bounds hn).1 (restartExpCoordinates_derivative_bounds hn).2
    (HB _ hy).2.1 (HB _ hy).2.2
  change ‖fderiv ℝ restartMixedWeakRates y‖ ≤ B * 1 ∧
    ‖fderiv ℝ (fderiv ℝ restartMixedWeakRates) y‖ ≤ B * 1 + B * 1 ^ 2 at H
  refine ⟨(HA _ hy).1.trans (mul_le_mul_of_nonneg_right hA (norm_nonneg _)),
    (HA _ hy).2.trans hA,
    (HB _ hy).1.trans (mul_le_mul_of_nonneg_right hBC (norm_nonneg _)),
    by nlinarith only [H.1, hBC], by nlinarith only [H.2, h2B], ?_⟩
  exact hbox.2.2.2.2.2

end BianchiIX
