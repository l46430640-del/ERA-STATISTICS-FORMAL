import BianchiIX.Dynamics.ProjectiveCycleDifferential
import BianchiIX.Algebra.ExitCycleQuotientBounds
import BianchiIX.Analysis.FiniteCoordinateBounds

noncomputable section

namespace BianchiIX

theorem cycleNumeratorSlope_basis_bound (i j : Fin 4) :
    |cycleNumeratorSlope i (Pi.single j 1)| ≤ 4 := by
  fin_cases i <;> fin_cases j <;> norm_num [cycleNumeratorSlope, Pi.single_apply, Fin.ext_iff]

theorem cycleDenomHessian_basis_bound (i j : Fin 4) :
    |cycleDenomHessian (Pi.single i 1) (Pi.single j 1)| ≤ 2 := by
  fin_cases i <;> fin_cases j <;> norm_num [cycleDenomHessian, Pi.single_apply, Fin.ext_iff]

theorem cycle_terminal_coefficient_bounds {α : ℝ} {y : ProjectiveState}
    (hm : |y 0 + 1| ≤ 3 * α) (hw : |y 1| + |y 2| + |y 3| ≤ 3 * α) :
    (∀ i : Fin 4, |cycleNumerator i y| ≤ 12 * α) ∧
      (∀ j : Fin 4, |cycleDenomDifferential y (Pi.single j 1)| ≤ 6 * α) := by
  have hthree {a b c : ℝ} (hs : |a| + |b| + |c| ≤ 3 * α) : |a - b - c| ≤ 3 * α := by
    linarith only [abs_sub (a - b) c, abs_sub a b, hs]
  have H1 := hthree hw
  have H2 := hthree (a := y 2) (b := y 1) (c := y 3) (by linarith only [hw])
  have H3 := hthree (a := y 3) (b := y 1) (c := y 2) (by linarith only [hw])
  constructor
  · intro i
    fin_cases i <;> norm_num [cycleNumerator, abs_mul] <;>
      linarith only [hm, hw, abs_nonneg (y 1), abs_nonneg (y 2), abs_nonneg (y 3)]
  · intro j
    fin_cases j <;> norm_num [cycleDenomDifferential, Pi.single_apply, Fin.ext_iff, abs_mul] <;>
      linarith only [hm, H1, H2, H3]

/-- D.20 is a bound on the actual first and second Frechet derivatives, not on formal coefficient arrays. -/
theorem projectiveCycle_terminal_derivative_bounds {α : ℝ} {y : ProjectiveState} (hα : 0 < α)
    (hH : 39 / 10 * α ^ 2 ≤ projectiveCycleDenom y)
    (hm : |y 0 + 1| ≤ 3 * α) (hw : |y 1| + |y 2| + |y 3| ≤ 3 * α) :
    (∀ i j : Fin 4, |fderiv ℝ (fun z => projectiveCycle z i) y (Pi.single j 1)| ≤ 6 / α ^ 2) ∧
      (∀ i j k : Fin 4, |fderiv ℝ (fderiv ℝ (fun z => projectiveCycle z i)) y
        (Pi.single j 1) (Pi.single k 1)| ≤ 20 / α ^ 3) := by
  have hH0 : projectiveCycleDenom y ≠ 0 := (lt_of_lt_of_le (by positivity) hH).ne'
  obtain ⟨HN, HD⟩ := cycle_terminal_coefficient_bounds hm hw
  constructor
  · intro i j
    rw [projectiveCycle_fderiv_component hH0]
    exact exitCycle_quotient_first_bound hα hH (HN i) (cycleNumeratorSlope_basis_bound i j) (HD j)
  · intro i j k
    rw [projectiveCycle_fderiv2_component hH0]
    exact exitCycle_quotient_second_bound hα hH (HN i)
      (cycleNumeratorSlope_basis_bound i j) (cycleNumeratorSlope_basis_bound i k) (HD j) (HD k)
      (cycleDenomHessian_basis_bound j k)

theorem projectiveCycle_terminal_operator_bounds {α : ℝ} {y : ProjectiveState} (hα : 0 < α)
    (hH : 39 / 10 * α ^ 2 ≤ projectiveCycleDenom y)
    (hm : |y 0 + 1| ≤ 3 * α) (hw : |y 1| + |y 2| + |y 3| ≤ 3 * α) (i : Fin 4) :
    ‖fderiv ℝ (fun z => projectiveCycle z i) y‖ ≤ 24 / α ^ 2 ∧
      ‖fderiv ℝ (fderiv ℝ (fun z => projectiveCycle z i)) y‖ ≤ 320 / α ^ 3 := by
  obtain ⟨H1, H2⟩ := projectiveCycle_terminal_derivative_bounds hα hH hm hw
  constructor
  · convert clm_norm_le_card_mul_basis_bound (fderiv ℝ (fun z => projectiveCycle z i) y)
      (by positivity : 0 ≤ 6 / α ^ 2) (H1 i) using 1
    norm_num
    ring
  · convert bilinear_norm_le_card_mul_basis_bound (fderiv ℝ (fderiv ℝ (fun z => projectiveCycle z i)) y)
      (by positivity : 0 ≤ 20 / α ^ 3) (H2 i) using 1
    norm_num
    ring

theorem projectiveCycle_log_denom_derivative_bound {α : ℝ} {y : ProjectiveState} (hα : 0 < α)
    (hH : 39 / 10 * α ^ 2 ≤ projectiveCycleDenom y)
    (hm : |y 0 + 1| ≤ 3 * α) (hw : |y 1| + |y 2| + |y 3| ≤ 3 * α) :
    ‖fderiv ℝ (fun z => Real.log (projectiveCycleDenom z)) y‖ ≤ 7 / α := by
  have hH0 : 0 < projectiveCycleDenom y := lt_of_lt_of_le (by positivity) hH
  have HD := (cycle_terminal_coefficient_bounds hm hw).2
  have HN := clm_norm_le_card_mul_basis_bound (fderiv ℝ projectiveCycleDenom y)
    (show 0 ≤ 6 * α by positivity) (fun j => by
      rw [Real.norm_eq_abs, projectiveCycleDenom_fderiv]
      exact HD j)
  have HN' : ‖fderiv ℝ projectiveCycleDenom y‖ ≤ 24 * α := by norm_num at HN; linarith only [HN]
  have hd := ((contDiff_projectiveCycleDenom 1).differentiable (by norm_num) y).hasFDerivAt
  rw [(hd.log hH0.ne').fderiv, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hH0]
  calc
    _ ≤ (projectiveCycleDenom y)⁻¹ * (24 * α) := mul_le_mul_of_nonneg_left HN' (inv_nonneg.mpr hH0.le)
    _ = 24 * α / projectiveCycleDenom y := by ring
    _ ≤ 7 / α := by
      apply (div_le_div_iff₀ hH0 hα).mpr
      nlinarith only [hH, sq_nonneg α]

end BianchiIX
