import BianchiIX.Dynamics.StableBoundaryStableBlock

noncomputable section

namespace BianchiIX

theorem stableBoundaryDenom_lower {y : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 10) :
    (c + 1) ^ 2 ≤ 3 * stableBoundaryDenom y ∧ c + 1 ≤ stableBoundaryDenom y := by
  obtain ⟨hK, hml, hm0, _, _, _⟩ := stable_boundary_band hc hm
  have hm2 := (sq_le_sq₀ (by positivity : 0 ≤ (5 / 8 : ℝ) * (c + 1)) hm0).mpr hml
  unfold stableBoundaryDenom
  constructor
  · nlinarith [sq_nonneg (y 1 - y 2)]
  · nlinarith [sq_nonneg (y 1 - y 2), sq_nonneg (c + 1 - 3)]

theorem stableBoundary_phase_div_bound {y : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 10) :
    |stableBoundaryField y 0 / stableBoundaryDenom y| ≤ (|y 1| + |y 2|) ^ 2 := by
  have hK : 0 < c + 1 := by linarith
  have hD := stableBoundaryDenom_pos y
  have H := stable_boundary_phase_bound (u := y 1) (w := y 2) hc hm
  have hw : y 2 ^ 2 / (c + 1) ≤ y 2 ^ 2 :=
    div_le_self (sq_nonneg _) (by linarith)
  have H' : |stableBoundaryField y 0 / (c + 1)| ≤ (|y 1| + |y 2|) ^ 2 := by
    rw [(stable_boundary_field (y 0) (y 1) (y 2)).1] at H
    change |stableBoundaryField y 0 / (c + 1)| ≤ _ at H
    nlinarith [sq_abs (y 1), sq_abs (y 2)]
  rw [abs_div, abs_of_pos hK] at H'
  have H'' := (div_le_iff₀ hK).mp H'
  rw [abs_div, abs_of_pos hD]
  apply (div_le_iff₀ hD).mpr
  exact H''.trans (mul_le_mul_of_nonneg_left (stableBoundaryDenom_lower hc hm).2 (sq_nonneg _))

theorem stableBoundary_polynomial_center_bounds {y : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 10) :
    |stableBoundaryJacobian y 0 0| ≤ (|y 1| + |y 2|) ^ 2 ∧
    |stableBoundaryJacobian y 0 1| ≤ 2 * (c + 1) * (|y 1| + |y 2|) ∧
    |stableBoundaryJacobian y 0 2| ≤ 2 * (c + 1) * (|y 1| + |y 2|) := by
  obtain ⟨hK, _, hm0, hmK, hm1, hm1K⟩ := stable_boundary_band hc hm
  constructor
  · change |y 1 ^ 2 - y 1 * y 2| ≤ _
    have H := abs_sub (y 1 ^ 2) (y 1 * y 2)
    rw [abs_of_nonneg (sq_nonneg (y 1)), abs_mul] at H
    nlinarith [sq_abs (y 1), sq_abs (y 2), mul_nonneg (abs_nonneg (y 1)) (abs_nonneg (y 2))]
  constructor
  · change |2 * y 0 * y 1 - (y 0 + 1) * y 2| ≤ _
    have H := abs_sub (2 * y 0 * y 1) ((y 0 + 1) * y 2)
    simp only [abs_mul, abs_of_nonneg hm0, abs_of_nonneg hm1,
      abs_of_pos (by norm_num : (0 : ℝ) < 2)] at H
    nlinarith [mul_le_mul_of_nonneg_right hmK (abs_nonneg (y 1)),
      mul_le_mul_of_nonneg_right hm1K (abs_nonneg (y 2))]
  · change |-(y 0 + 1) * y 1 + 2 * y 2| ≤ _
    have H := abs_add_le (-(y 0 + 1) * y 1) (2 * y 2)
    rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg hm1, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at H
    nlinarith [mul_le_mul_of_nonneg_right hm1K (abs_nonneg (y 1)),
      mul_nonneg (by linarith : 0 ≤ c) (abs_nonneg (y 2))]

private theorem stable_scaled_entry_bound {y : StableState} {c B : ℝ} {i j : Fin 3}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 10) (hB : 0 ≤ B)
    (hentry : |stableBoundaryJacobian y i j -
      stableBoundaryField y i / stableBoundaryDenom y * stableDenomGradient y j| ≤ 3 * (c + 1) * B) :
    |(c + 1) * stableOriginalJacobian y i j| ≤ 64 * B := by
  have hK : 0 < c + 1 := by linarith
  have hD := stableBoundaryDenom_pos y
  have hscale : 6 * (c + 1) ^ 2 / stableBoundaryDenom y ≤ 18 := by
    apply (div_le_iff₀ hD).mpr
    nlinarith [(stableBoundaryDenom_lower hc hm).1]
  rw [stableOriginalJacobian_factor, abs_mul, abs_of_pos hK, abs_mul,
    abs_of_pos (by positivity : 0 < 6 / stableBoundaryDenom y)]
  calc
    _ ≤ (c + 1) * (6 / stableBoundaryDenom y * (3 * (c + 1) * B)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hentry (by positivity)) hK.le
    _ = (6 * (c + 1) ^ 2 / stableBoundaryDenom y) * (3 * B) := by ring
    _ ≤ 18 * (3 * B) := mul_le_mul_of_nonneg_right hscale (by positivity)
    _ ≤ 64 * B := by linarith

theorem stableRescaledJacobian_center_bounds {y : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 10)
    (hu : |y 1| ≤ 1 / 100) (hw : |y 2| ≤ 1 / 100) :
    |(c + 1) * stableOriginalJacobian y 0 0| ≤ 64 * (|y 1| + |y 2|) ^ 2 ∧
    |(c + 1) * stableOriginalJacobian y 0 1| ≤ 64 * (|y 1| + |y 2|) ∧
    |(c + 1) * stableOriginalJacobian y 0 2| ≤ 64 * (|y 1| + |y 2|) := by
  obtain ⟨hK, _, hm0, hmK, _, _⟩ := stable_boundary_band hc hm
  have hb : 0 ≤ |y 1| + |y 2| := by positivity
  have hb1 : |y 1| + |y 2| ≤ 1 := by linarith
  have hb2 : (|y 1| + |y 2|) ^ 2 ≤ 1 := by
    simpa using (sq_le_sq₀ hb (by norm_num : (0 : ℝ) ≤ 1)).mpr hb1
  have hf := stableBoundary_phase_div_bound hc hm
  obtain ⟨h00, h01, h02⟩ := stableBoundary_polynomial_center_bounds hc hm
  have hg0 : |stableDenomGradient y 0| ≤ 2 * (c + 1) := by
    change |2 * y 0| ≤ _
    rw [abs_of_nonneg (by positivity)]
    linarith
  have hg1 : |stableDenomGradient y 1| ≤ 2 * (|y 1| + |y 2|) := by
    change |2 * (y 1 - y 2)| ≤ _
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact mul_le_mul_of_nonneg_left (abs_sub _ _) (by norm_num)
  have hg2 : |stableDenomGradient y 2| ≤ 2 * (|y 1| + |y 2|) := by
    change |2 * (y 2 - y 1)| ≤ _
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have H := abs_sub (y 2) (y 1)
    linarith
  have hfg0 : |stableBoundaryField y 0 / stableBoundaryDenom y * stableDenomGradient y 0| ≤
      2 * (c + 1) * (|y 1| + |y 2|) ^ 2 := by
    rw [abs_mul]
    nlinarith [mul_le_mul hf hg0 (abs_nonneg _) (sq_nonneg _)]
  have hfg (j : Fin 3) (hg : |stableDenomGradient y j| ≤ 2 * (|y 1| + |y 2|)) :
      |stableBoundaryField y 0 / stableBoundaryDenom y * stableDenomGradient y j| ≤
        2 * (|y 1| + |y 2|) := by
    rw [abs_mul]
    nlinarith [mul_le_mul (hf.trans hb2) hg (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)]
  constructor
  · apply stable_scaled_entry_bound hc hm (sq_nonneg _)
    have H := abs_sub (stableBoundaryJacobian y 0 0)
      (stableBoundaryField y 0 / stableBoundaryDenom y * stableDenomGradient y 0)
    nlinarith [mul_nonneg (by linarith : 0 ≤ c) (sq_nonneg (|y 1| + |y 2|))]
  constructor
  · apply stable_scaled_entry_bound hc hm hb
    have H := abs_sub (stableBoundaryJacobian y 0 1)
      (stableBoundaryField y 0 / stableBoundaryDenom y * stableDenomGradient y 1)
    nlinarith [hfg 1 hg1, mul_nonneg (by linarith : 0 ≤ c - 1) hb]
  · apply stable_scaled_entry_bound hc hm hb
    have H := abs_sub (stableBoundaryJacobian y 0 2)
      (stableBoundaryField y 0 / stableBoundaryDenom y * stableDenomGradient y 2)
    nlinarith [hfg 2 hg2, mul_nonneg (by linarith : 0 ≤ c - 1) hb]

theorem stableRescaledJacobian_center_column {y : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 10)
    (hu : |y 1| ≤ 1 / 100) (hw : |y 2| ≤ 1 / 100) :
    |(c + 1) * stableOriginalJacobian y 1 0| ≤ 64 * |y 1| ∧
    |(c + 1) * stableOriginalJacobian y 2 0| ≤ 64 * |y 2| := by
  obtain ⟨hK, _, hm0, hmK, _, _⟩ := stable_boundary_band hc hm
  have H := stableBoundary_field_div_bounds hc hm hu hw
  have hg : |stableDenomGradient y 0| ≤ 2 * (c + 1) := by
    change |2 * y 0| ≤ _
    rw [abs_of_nonneg (by positivity)]
    linarith
  constructor
  · apply stable_scaled_entry_bound hc hm (abs_nonneg _)
    have hf : |stableBoundaryField y 1 / stableBoundaryDenom y * stableDenomGradient y 0| ≤
        2 * (c + 1) * |y 1| := by
      rw [abs_mul]
      nlinarith [mul_le_mul H.1 hg (abs_nonneg _) (abs_nonneg _)]
    have hp : |stableBoundaryJacobian y 1 0| ≤ (c + 1) * |y 1| := by
      change |-y 0 * y 1| ≤ _
      rw [abs_mul, abs_neg, abs_of_nonneg hm0]
      exact mul_le_mul_of_nonneg_right hmK (abs_nonneg _)
    have H' := abs_sub (stableBoundaryJacobian y 1 0)
      (stableBoundaryField y 1 / stableBoundaryDenom y * stableDenomGradient y 0)
    linarith
  · apply stable_scaled_entry_bound hc hm (abs_nonneg _)
    have hf : |stableBoundaryField y 2 / stableBoundaryDenom y * stableDenomGradient y 0| ≤
        2 * (c + 1) * |y 2| := by
      rw [abs_mul]
      nlinarith [mul_le_mul H.2 hg (abs_nonneg _) (abs_nonneg _)]
    have hp : |stableBoundaryJacobian y 2 0| ≤ (c + 1) * |y 2| := by
      change |-y 2| ≤ _
      rw [abs_neg]
      nlinarith [abs_nonneg (y 2)]
    have H' := abs_sub (stableBoundaryJacobian y 2 0)
      (stableBoundaryField y 2 / stableBoundaryDenom y * stableDenomGradient y 0)
    linarith

end BianchiIX
