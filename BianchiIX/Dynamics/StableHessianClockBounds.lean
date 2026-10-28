import BianchiIX.Dynamics.StableOriginalHessian
import BianchiIX.Dynamics.StableBoundaryCoupling

noncomputable section

namespace BianchiIX

theorem stableOriginalHessian_factor (y v w : StableState) :
    stableOriginalHessian y v w =
      (6 / stableBoundaryDenom y) • stableBoundaryHessian y v w -
        (dotProduct (stableDenomGradient y) v / stableBoundaryDenom y) •
          (stableOriginalJacobian y).mulVec w -
        (dotProduct (stableDenomGradient y) w / stableBoundaryDenom y) •
          (stableOriginalJacobian y).mulVec v -
        (stableDenomHessian v w / stableBoundaryDenom y) • stableOriginalField y := by
  simp only [stableOriginalJacobian_mulVec]
  ext i
  dsimp [stableOriginalHessian, stableOriginalField]
  field_simp
  ring

theorem stableBoundaryField_div_component {y : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 10)
    (hu : |y 1| ≤ 1 / 100) (hw : |y 2| ≤ 1 / 100) (i : Fin 3) :
    |stableBoundaryField y i / stableBoundaryDenom y| ≤ |y 1| + |y 2| := by
  have hb : 0 ≤ |y 1| + |y 2| := by positivity
  have hb1 : |y 1| + |y 2| ≤ 1 := by linarith
  have H := stableBoundary_field_div_bounds hc hm hu hw
  fin_cases i
  · exact (stableBoundary_phase_div_bound hc hm).trans (by nlinarith)
  · exact H.1.trans (by linarith [abs_nonneg (y 2)])
  · exact H.2.trans (by linarith [abs_nonneg (y 1)])

theorem stableOriginalField_norm_bound {y : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 10)
    (hu : |y 1| ≤ 1 / 100) (hw : |y 2| ≤ 1 / 100) :
    ‖stableOriginalField y‖ ≤ 6 * (|y 1| + |y 2|) := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  rw [Real.norm_eq_abs]
  change |(6 / stableBoundaryDenom y) * stableBoundaryField y i| ≤ _
  rw [show (6 / stableBoundaryDenom y) * stableBoundaryField y i =
    6 * (stableBoundaryField y i / stableBoundaryDenom y) by ring, abs_mul]
  norm_num only
  exact mul_le_mul_of_nonneg_left (stableBoundaryField_div_component hc hm hu hw i) (by norm_num)

theorem stableDenomGradient_wall_bound (y : StableState) (j : Fin 3) (hj : j ≠ 0) :
    |stableDenomGradient y j| ≤ 2 * (|y 1| + |y 2|) := by
  fin_cases j
  · exact (hj rfl).elim
  · change |2 * (y 1 - y 2)| ≤ _
    rw [abs_mul]
    norm_num only
    exact mul_le_mul_of_nonneg_left (abs_sub _ _) (by norm_num)
  · change |2 * (y 2 - y 1)| ≤ _
    rw [abs_mul]
    norm_num only
    have H := abs_sub (y 2) (y 1)
    linarith

theorem stableDenomGradient_bound {y : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 10)
    (hu : |y 1| ≤ 1 / 100) (hw : |y 2| ≤ 1 / 100) (v : StableState) :
    |dotProduct (stableDenomGradient y) v| ≤ 6 * (c + 1) * ‖v‖ := by
  obtain ⟨hK, _, hm0, hmK, _, _⟩ := stable_boundary_band hc hm
  have hg (j : Fin 3) : |stableDenomGradient y j| ≤ 2 * (c + 1) := by
    by_cases hj : j = 0
    · subst j
      change |2 * y 0| ≤ _
      rw [abs_of_nonneg (by positivity)]
      linarith
    · exact (stableDenomGradient_wall_bound y j hj).trans (by linarith)
  have hv (j : Fin 3) : |v j| ≤ ‖v‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm v j
  have hprod (j : Fin 3) : |stableDenomGradient y j * v j| ≤ 2 * (c + 1) * ‖v‖ := by
    rw [abs_mul]
    exact mul_le_mul (hg j) (hv j) (abs_nonneg _) (by positivity)
  calc
    _ ≤ ∑ j, |stableDenomGradient y j * v j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin 3, 2 * (c + 1) * ‖v‖ := Finset.sum_le_sum (fun j _ => hprod j)
    _ = _ := by simp; ring

theorem stableDenomHessian_bound (v w : StableState) :
    |stableDenomHessian v w| ≤ 10 * ‖v‖ * ‖w‖ := by
  have hv (j : Fin 3) : |v j| ≤ ‖v‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm v j
  have hw (j : Fin 3) : |w j| ≤ ‖w‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm w j
  have hvd : |v 1 - v 2| ≤ 2 * ‖v‖ := (abs_sub _ _).trans (by linarith [hv 1, hv 2])
  have hwd : |w 1 - w 2| ≤ 2 * ‖w‖ := (abs_sub _ _).trans (by linarith [hw 1, hw 2])
  have H0 := mul_le_mul (hv 0) (hw 0) (abs_nonneg _) (norm_nonneg _)
  have H1 := mul_le_mul hvd hwd (abs_nonneg _) (by positivity)
  have H := abs_add_le (2 * v 0 * w 0) (2 * (v 1 - v 2) * (w 1 - w 2))
  simp only [abs_mul] at H
  norm_num only at H
  change |stableDenomHessian v w| ≤ _ at H
  nlinarith only [H, H0, H1]

theorem stableBoundaryJacobian_wall_bound {y : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 10)
    (hu : |y 1| ≤ 1 / 100) (hw : |y 2| ≤ 1 / 100) (i j : Fin 3) (hj : j ≠ 0) :
    |stableBoundaryJacobian y i j| ≤ 2 * stableBoundaryDenom y := by
  have hD3 : 3 ≤ stableBoundaryDenom y := by
    unfold stableBoundaryDenom
    nlinarith [sq_nonneg (y 0), sq_nonneg (y 1 - y 2)]
  have hKD := (stableBoundaryDenom_lower hc hm).2
  have hK : 0 ≤ c + 1 := by linarith
  have hb : |y 1| + |y 2| ≤ 1 := by linarith
  have hu2 : y 1 ^ 2 ≤ 1 := by nlinarith [sq_abs (y 1), abs_nonneg (y 1)]
  have hw2 : y 2 ^ 2 ≤ 1 := by nlinarith [sq_abs (y 2), abs_nonneg (y 2)]
  have huw : |y 1 * y 2| ≤ 1 := by
    rw [abs_mul]
    nlinarith [mul_le_mul hu hw (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 / 100)]
  have hcenter := stableBoundary_polynomial_center_bounds hc hm
  have hcenter' : 2 * (c + 1) * (|y 1| + |y 2|) ≤ 2 * stableBoundaryDenom y := by
    nlinarith [mul_le_of_le_one_right (show 0 ≤ 2 * (c + 1) by positivity) hb]
  have hrate := stableBoundary_rate_denom_bounds hc hm hu hw
  fin_cases i <;> fin_cases j
  · exact (hj rfl).elim
  · exact hcenter.2.1.trans hcenter'
  · exact hcenter.2.2.trans hcenter'
  · exact (hj rfl).elim
  · change |(1 - y 0 ^ 2 - y 2 ^ 2 + 3 * y 1 ^ 2) / 2| ≤ _
    have heq : (1 - y 0 ^ 2 - y 2 ^ 2 + 3 * y 1 ^ 2) / 2 =
        stableStrongRate (y 0) (y 1) (y 2) + y 1 ^ 2 := by
      unfold stableStrongRate; ring
    rw [heq]
    have H := abs_add_le (stableStrongRate (y 0) (y 1) (y 2)) (y 1 ^ 2)
    rw [abs_of_nonneg (sq_nonneg (y 1))] at H
    linarith
  · change |-y 1 * y 2| ≤ _
    rw [neg_mul, abs_neg]
    linarith
  · exact (hj rfl).elim
  · change |(2 * y 1 - y 2) * y 2| ≤ _
    have heq : (2 * y 1 - y 2) * y 2 = 2 * (y 1 * y 2) - y 2 ^ 2 := by ring
    rw [heq]
    have H := abs_sub (2 * (y 1 * y 2)) (y 2 ^ 2)
    rw [abs_mul, abs_of_nonneg (sq_nonneg (y 2))] at H
    norm_num only at H
    linarith
  · change |-(y 0 + 1 + 2 * y 1 * y 2 - y 1 ^ 2)| ≤ _
    have heq : -(y 0 + 1 + 2 * y 1 * y 2 - y 1 ^ 2) =
        stableWeakRate (y 0) (y 1) (y 2) - y 1 * y 2 := by
      unfold stableWeakRate; ring
    rw [heq]
    have H := abs_sub (stableWeakRate (y 0) (y 1) (y 2)) (y 1 * y 2)
    linarith

theorem stableOriginalJacobian_wall_bound {y : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 10)
    (hu : |y 1| ≤ 1 / 100) (hw : |y 2| ≤ 1 / 100) (i j : Fin 3) (hj : j ≠ 0) :
    |stableOriginalJacobian y i j| ≤ 18 := by
  have hD := stableBoundaryDenom_pos y
  have hD3 : 3 ≤ stableBoundaryDenom y := by
    unfold stableBoundaryDenom
    nlinarith [sq_nonneg (y 0), sq_nonneg (y 1 - y 2)]
  have hb : 0 ≤ |y 1| + |y 2| := by positivity
  have hb1 : |y 1| + |y 2| ≤ 1 := by linarith
  have hprod : |stableBoundaryField y i / stableBoundaryDenom y * stableDenomGradient y j| ≤ 2 := by
    rw [abs_mul]
    have H := mul_le_mul (stableBoundaryField_div_component hc hm hu hw i)
      (stableDenomGradient_wall_bound y j hj) (abs_nonneg _) hb
    nlinarith
  have H := abs_sub (stableBoundaryJacobian y i j)
    (stableBoundaryField y i / stableBoundaryDenom y * stableDenomGradient y j)
  have hbracket : |stableBoundaryJacobian y i j -
      stableBoundaryField y i / stableBoundaryDenom y * stableDenomGradient y j| ≤
      3 * stableBoundaryDenom y := by
    linarith [stableBoundaryJacobian_wall_bound hc hm hu hw i j hj]
  rw [stableOriginalJacobian_factor, abs_mul, abs_of_pos (by positivity : 0 < 6 / stableBoundaryDenom y)]
  calc
    _ ≤ (6 / stableBoundaryDenom y) * (3 * stableBoundaryDenom y) :=
      mul_le_mul_of_nonneg_left hbracket (by positivity)
    _ = 18 := by field_simp; norm_num

end BianchiIX
