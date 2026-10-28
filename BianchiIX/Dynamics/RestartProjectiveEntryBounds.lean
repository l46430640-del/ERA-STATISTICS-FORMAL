import BianchiIX.Dynamics.RestartFastProjectionHeight

noncomputable section

namespace BianchiIX

theorem coreAngle_toProjectiveState {x : NormalizedState} (hA : 1 + x 0 ≠ 0) :
    coreAngle (toProjectiveState x 0) (toProjectiveState x 2) =
      Real.arsinh (((1 + x 0) / Real.sqrt 3 - x 1) / x 3) := by
  change Real.arsinh ((1 - Real.sqrt 3 * x 1 / (1 + x 0)) /
    (Real.sqrt 3 * x 3 / (1 + x 0))) = _
  congr 1
  have hsqrt : Real.sqrt (3 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  by_cases ha : x 3 = 0
  · simp [ha]
  · field_simp

/-- The projective entry scales follow from the quadratic height and linear active wall. -/
theorem restartProjectiveEntry_bounds {x : NormalizedState} {r M : ℝ}
    (hr : 0 < r) (hM : 0 ≤ M) (hsmall : M * r ≤ 1 / 16)
    (hAlo : r ^ 2 / 16 ≤ 1 + x 0) (hAhi : 1 + x 0 ≤ 10 * (M * r) ^ 2)
    (hs : |x 1| ≤ M * r) (ha : r / 2 ≤ x 3 ∧ x 3 ≤ M * r)
    (hn : 0 ≤ x 2) (hb : 0 ≤ x 4) :
    1 / (20 * M ^ 2 * r) ≤ toProjectiveState x 2 ∧
      toProjectiveState x 2 ≤ 32 * M / r ∧
      (0 ≤ toProjectiveState x 1 ∧ toProjectiveState x 1 ≤ 32 * x 2 / r ^ 2) ∧
      (0 ≤ toProjectiveState x 3 ∧ toProjectiveState x 3 ≤ 32 * x 4 / r ^ 2) ∧
      |coreAngle (toProjectiveState x 0) (toProjectiveState x 2)| ≤ Real.arsinh (4 * M) := by
  have hA : 0 < 1 + x 0 := lt_of_lt_of_le (by positivity) hAlo
  have ha0 : 0 < x 3 := by linarith only [hr, ha.1]
  have hM0 : 0 < M := by nlinarith only [ha.1, ha.2, hr]
  have hsqrt : 0 < Real.sqrt (3 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hsqrtSq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hsqrt1 : 1 ≤ Real.sqrt (3 : ℝ) := by nlinarith only [hsqrtSq, hsqrt]
  have hsqrt2 : Real.sqrt (3 : ℝ) ≤ 2 := by nlinarith only [hsqrtSq, hsqrt]
  have Hcoord (u : ℝ) (hu : 0 ≤ u) :
      0 ≤ Real.sqrt 3 * u / (1 + x 0) ∧ Real.sqrt 3 * u / (1 + x 0) ≤ 32 * u / r ^ 2 := by
    refine ⟨by positivity, ?_⟩
    calc
      _ ≤ 2 * u / (r ^ 2 / 16) :=
        div_le_div₀ (mul_nonneg (by norm_num) hu) (mul_le_mul_of_nonneg_right hsqrt2 hu) (by positivity) hAlo
      _ = _ := by ring
  refine ⟨?_, ?_, Hcoord (x 2) hn, Hcoord (x 4) hb, ?_⟩
  · change _ ≤ Real.sqrt 3 * x 3 / (1 + x 0)
    calc
      _ = (r / 2) / (10 * (M * r) ^ 2) := by field_simp; ring
      _ ≤ Real.sqrt 3 * x 3 / (1 + x 0) :=
        div_le_div₀ (by positivity) (by nlinarith only [ha.1, mul_le_mul_of_nonneg_right hsqrt1 ha0.le]) hA hAhi
  · exact (Hcoord (x 3) ha0.le).2.trans (by
      apply (div_le_iff₀ (sq_pos_of_pos hr)).mpr
      have heq : 32 * M / r * r ^ 2 = 32 * (M * r) := by field_simp
      rw [heq]
      linarith only [ha.2])
  · rw [coreAngle_toProjectiveState (ne_of_gt hA)]
    have HAr : 1 + x 0 ≤ M * r := by
      have H := mul_le_mul_of_nonneg_right hsmall (mul_nonneg hM hr.le)
      nlinarith only [hAhi, H, mul_nonneg hM hr.le]
    have HAs : (1 + x 0) / Real.sqrt 3 ≤ M * r :=
      (div_le_self hA.le hsqrt1).trans HAr
    have Hnum : |(1 + x 0) / Real.sqrt 3 - x 1| ≤ 2 * M * r := by
      have H := abs_sub_le ((1 + x 0) / Real.sqrt 3) 0 (x 1)
      simp only [sub_zero, zero_sub, abs_neg, abs_of_pos (div_pos hA hsqrt)] at H
      linarith only [H, HAs, hs]
    have Harg : |((1 + x 0) / Real.sqrt 3 - x 1) / x 3| ≤ 4 * M := by
      rw [abs_div, abs_of_pos ha0]
      apply (div_le_iff₀ ha0).mpr
      nlinarith only [Hnum, mul_le_mul_of_nonneg_left ha.1 hM]
    apply abs_le.mpr
    constructor
    · rw [← Real.arsinh_neg]
      exact Real.arsinh_le_arsinh.mpr (abs_le.mp Harg).1
    · exact Real.arsinh_le_arsinh.mpr (abs_le.mp Harg).2

end BianchiIX
