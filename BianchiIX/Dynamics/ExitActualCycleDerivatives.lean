import BianchiIX.Dynamics.ProjectiveCycleDerivativeBounds
import BianchiIX.Dynamics.ExitActualCycleEndpoint

noncomputable section

namespace BianchiIX

theorem exists_terminal_axisCycle_derivatives {η : ℝ} (hη : 0 < η ∧ η ≤ 1 / 100)
    {J : ℕ} (hJ : 2 ≤ J) :
    ∃ ε > (0 : ℝ), ∀ α b u w : ℝ,
      (0 < α ∧ α ≤ 1) → 0 < b → b ≤ ε * α ^ (2 * J) → |u| + |w| ≤ b →
      let Y : ExitTailState := ![2 + 2 * α, u, w]
      let h := η * α ^ J
      let y := coreTailState h Y
      coreTailValid h Y ∧
        (∀ i j : Fin 4, |fderiv ℝ (fun z => projectiveCycle z i) y (Pi.single j 1)| ≤ 6 / α ^ 2) ∧
        (∀ i j k : Fin 4, |fderiv ℝ (fderiv ℝ (fun z => projectiveCycle z i)) y
          (Pi.single j 1) (Pi.single k 1)| ≤ 20 / α ^ 3) ∧
        (∀ i : Fin 4, ‖fderiv ℝ (fun z => projectiveCycle z i) y‖ ≤ 24 / α ^ 2 ∧
          ‖fderiv ℝ (fderiv ℝ (fun z => projectiveCycle z i)) y‖ ≤ 320 / α ^ 3) ∧
        ‖fderiv ℝ (fun z => Real.log (projectiveCycleDenom z)) y‖ ≤ 7 / α := by
  obtain ⟨A, hA, ε, hε, HE⟩ := exists_terminal_axisCycle_regular hη (by omega : 1 ≤ J)
  refine ⟨ε, hε, ?_⟩
  intro α b u w hα hb hsmall hsum Y h y
  have H := HE α b u w hα hb hsmall hsum
  have HV : coreTailValid h Y := H.1
  have Ht := H.2.2.1 (coreTailTime h Y) ⟨HV.1.1.1.le, le_rfl⟩
  have hR : |coreRadius (y 0) (y 2) - (2 + 2 * α)| ≤ A * b := Ht.2.1
  have hW : |y 1| + |y 3| ≤ A * b := Ht.2.2.1
  have hB : A * b ≤ α / 10000 := H.2.1.trans
    (div_le_div_of_nonneg_right
      ((pow_le_pow_of_le_one hα.1.le hα.2 (by omega : 1 ≤ 2 * J)).trans_eq (pow_one α)) (by norm_num))
  have hv : 0 ≤ y 2 ∧ y 2 ≤ α / 100 := by
    change 0 ≤ coreTailState h Y 2 ∧ coreTailState h Y 2 ≤ _
    rw [coreTailState_active HV]
    refine ⟨mul_nonneg hη.1.le (pow_nonneg hα.1.le J), ?_⟩
    have hp := (pow_le_pow_of_le_one hα.1.le hα.2 (by omega : 1 ≤ J)).trans_eq (pow_one α)
    change η * α ^ J ≤ _
    nlinarith only [mul_le_mul_of_nonneg_left hp hη.1.le, mul_le_mul_of_nonneg_right hη.2 hα.1.le]
  have HD := exitTailGap_terminal_offset hα hB hR hv
  rw [exitTailGap_of_coreRadius (show y 0 < 1 from Ht.1)] at HD
  have hm : |y 0 + 1| ≤ 3 * α := abs_le.mpr (by constructor <;> linarith only [HD.1, HD.2, hα.1])
  have hw' : |y 1| + |y 2| + |y 3| ≤ 3 * α := by
    rw [abs_of_nonneg hv.1]
    linarith only [hW, hB, hv.2, hα.1]
  have hH : 39 / 10 * α ^ 2 ≤ projectiveCycleDenom y := by
    have HH : 399 / 100 * α ^ 2 < projectiveCycleDenom y := H.2.2.2.1
    nlinarith only [HH, sq_nonneg α]
  obtain ⟨H1, H2⟩ := projectiveCycle_terminal_derivative_bounds hα.1 hH hm hw'
  exact ⟨HV, H1, H2, projectiveCycle_terminal_operator_bounds hα.1 hH hm hw',
    projectiveCycle_log_denom_derivative_bound hα.1 hH hm hw'⟩

end BianchiIX
