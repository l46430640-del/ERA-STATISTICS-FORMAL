import BianchiIX.Dynamics.ConnectionPhaseResponseFormula
import BianchiIX.Dynamics.ConnectionReturnDecay
import BianchiIX.Dynamics.ConnectionReturnAmplitudes
import BianchiIX.Analysis.ConnectionPhaseResponseBounds

noncomputable section

namespace BianchiIX

/-- The three ordinary phase-error derivatives of the exact positive-wall first return. -/
theorem connectionReturn_phase_response_bounds {p : ConnectionParameters} (hμ : 4 ≤ p 0)
    (hu : 0 < p 1 ∧ p 1 ≤ (1 / 10000) / p 0) (hw : 0 < p 2 ∧ p 2 ≤ 1 / 10000) :
    |fderiv ℝ connectionReturnPhaseError p ![1, 0, 0]| ≤ 50000 * (p 1 + (p 2) ^ 2) / (p 0) ^ 2 ∧
    |fderiv ℝ connectionReturnPhaseError p ![0, 1, 0]| ≤ 50000 / p 0 ∧
    |fderiv ℝ connectionReturnPhaseError p ![0, 0, 1]| ≤ 50000 * (p 1 + p 2) / p 0 := by
  let μ := p 0
  let u := p 1
  let w := p 2
  let L := -Real.log w
  let y := connectionReturnState p
  let J := fderiv ℝ (connectionLogCoordinates ∘ connectionReturnState) p
  let D := connectionLogFlowVariation (connectionEntry μ u w) 0 (connectionReturnTime p)
  have hμ0 : 0 < μ := by linarith only [hμ]
  have hu0 : 0 < u := hu.1
  have hw0 : 0 < w := hw.1
  have hL : 0 ≤ L := neg_nonneg.mpr (Real.log_nonpos hw0.le (by linarith only [hw.2]))
  have hrad : J ![1, 0, 0] = D ![-1, 0, 0, 0] := by
    simpa [J, D, μ, u, w] using connectionReturn_log_differential hμ hu hw ![1, 0, 0]
  have hstrong : J ![0, 1, 0] = D ![0, 1, 0, 0] := by
    simpa [J, D, μ, u, w] using connectionReturn_log_differential hμ hu hw ![0, 1, 0]
  have hgrowing : J ![0, 0, 1] = D ![0, 0, 0, 1] - (1 / w) • connectionLogCoordinateRates y := by
    simpa [J, D, y, μ, u, w] using connectionReturn_log_differential hμ hu hw ![0, 0, 1]
  have H := connectionReturn_fixed_clock_bounds hμ hu hw
  have HA := connectionReturn_log_amplitude_bounds hμ hu hw
  have HS := connectionReturn_endpoint_scales hμ hu hw
  have hc := connectionReturn_control hμ ⟨hu.1.le, hu.2⟩ hw
  have hr := (hc.2 (connectionReturnTime p) ⟨hc.1.le, le_rfl⟩).2
  change connectionRegion μ y at hr
  have hv2 : (y 2) ^ 2 ≤ w ^ 2 := HS.2.1
  have hweight : (1 + L) * (y 2) ^ 2 ≤ μ * w ^ 2 := HS.2.2
  have hzμ : |J ![1, 0, 0] 0| ≤ 16 / 15 := by rw [hrad]; exact H.1.1
  have hdμ : |J ![1, 0, 0] 0 - matchingPhaseSlope μ 1 w| ≤ 35000 * (u + w ^ 2) / μ ^ 2 := by
    rw [hrad]
    have H0 : |D ![-1, 0, 0, 0] 0 - matchingPhaseSlope μ 1 w| ≤
        (16 / 15) * connectionPhaseFeedbackBudget μ u w := by
      simpa [D, μ, u, w, connectionLogTangent, connectionEntry] using H.1.2.1
    exact H0.trans (connectionPhaseFeedbackBudget_scale hμ hu0.le)
  have hzU : |J ![0, 1, 0] 0| ≤ 70 / μ := by rw [hstrong]; exact H.2.1.1
  have hzW : |J ![0, 0, 1] 0| ≤ 8100 * (u + w) / μ := by
    rw [hgrowing]
    have Htri := abs_sub (D ![0, 0, 0, 1] 0) ((1 / w) * connectionLogCoordinateRates y 0)
    have Hc : |(1 / w) * connectionLogCoordinateRates y 0| ≤ 100 * (u + w) / μ := by
      simpa [abs_mul, abs_of_pos hw0, div_eq_mul_inv, mul_comm] using connectionReturn_phase_clock_correction hμ hu hw
    exact (Htri.trans (add_le_add H.2.2.1 Hc)).trans_eq (by ring)
  have hyμ : ((y 2) ^ 2 / μ) * |J ![1, 0, 0] 2| ≤ 137 * w ^ 2 / μ ^ 2 := by
    apply connection_endpoint_weighted_log_bound hμ0 (by norm_num) hweight
    exact HA.2.1.trans (div_le_div_of_nonneg_right (by nlinarith only [hL]) (sq_nonneg μ))
  have hyU : ((y 2) ^ 2 / μ) * |J ![0, 1, 0] 2| ≤ 9000 * w ^ 2 / μ ^ 2 :=
    connection_endpoint_weighted_log_bound hμ0 (by norm_num) hweight HA.2.2.2.1
  have hyW : ((y 2) ^ 2 / μ) * |J ![0, 0, 1] 2| ≤ 9 * w / μ := by
    have h32 : 32 / μ ≤ 8 := (div_le_iff₀ hμ0).mpr (by linarith only [hμ])
    have HY : |J ![0, 0, 1] 2| ≤ 9 / w := HA.2.2.2.2.2.trans
      (div_le_div_of_nonneg_right (by linarith only [h32]) hw0.le)
    calc
      _ ≤ ((y 2) ^ 2 / μ) * (9 / w) := mul_le_mul_of_nonneg_left HY (by positivity)
      _ ≤ (w ^ 2 / μ) * (9 / w) := mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right hv2 hμ0.le) (by positivity)
      _ = 9 * w / μ := by field_simp
  have hformula (v : ConnectionParameters) := connectionReturnPhaseError_differential hμ hu hw v
  have hsmall : w ^ 2 / μ ^ 2 ≤ 1 / μ := by
    have hw1 : w ≤ 1 := by linarith only [hw.2]
    have hw2 : w ^ 2 ≤ 1 := by nlinarith only [hw0, hw1]
    calc
      w ^ 2 / μ ^ 2 ≤ 1 / μ ^ 2 := div_le_div_of_nonneg_right hw2 (sq_nonneg μ)
      _ ≤ 1 / μ := div_le_div_of_nonneg_left (by norm_num) hμ0 (by nlinarith only [hμ])
  refine ⟨?_, ?_, ?_⟩
  · rw [hformula ![1, 0, 0]]
    simp only [Matrix.cons_val_zero, mul_one]
    have HB := connectionExitPhase_radial_error_bound (w := w) hμ hr.1 hr.2.2.1 (J ![1, 0, 0] 0) (J ![1, 0, 0] 2)
    apply HB.trans
    have Hsecond : (4 * (y 2) ^ 2 / μ ^ 2) * |J ![1, 0, 0] 0| ≤ 5 * w ^ 2 / μ ^ 2 := by
      have HB' := mul_le_mul (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hv2 (by norm_num)) (sq_nonneg μ))
        hzμ (abs_nonneg _) (show 0 ≤ 4 * w ^ 2 / μ ^ 2 by positivity)
      apply HB'.trans
      have hq : 0 ≤ w ^ 2 / μ ^ 2 := by positivity
      simp only [div_eq_mul_inv] at hq ⊢
      nlinarith only [hq]
    have HB' := add_le_add (add_le_add (add_le_add hdμ Hsecond)
      (mul_le_mul_of_nonneg_left hyμ (by norm_num : (0 : ℝ) ≤ 4 / 3))) (le_refl (2 * w ^ 2 / μ ^ 2))
    apply HB'.trans
    have hUq : 0 ≤ u / μ ^ 2 := by positivity
    have hWq : 0 ≤ w ^ 2 / μ ^ 2 := by positivity
    simp only [div_eq_mul_inv] at hUq hWq ⊢
    nlinarith only [hUq, hWq]
  · rw [hformula ![0, 1, 0]]
    simp only [Matrix.cons_val_zero, mul_zero, sub_zero]
    apply (connectionExitPhase_response_bound hμ hr.1 hr.2.2.1 (J ![0, 1, 0] 0) (J ![0, 1, 0] 2)).trans
    apply (mul_le_mul_of_nonneg_left (add_le_add hzU hyU) (by norm_num : (0 : ℝ) ≤ 4 / 3)).trans
    have hi : 0 ≤ 1 / μ := by positivity
    simp only [div_eq_mul_inv] at hsmall hi ⊢
    nlinarith only [hsmall, hi]
  · rw [hformula ![0, 0, 1]]
    simp only [Matrix.cons_val_zero, mul_zero, sub_zero]
    apply (connectionExitPhase_response_bound hμ hr.1 hr.2.2.1 (J ![0, 0, 1] 0) (J ![0, 0, 1] 2)).trans
    apply (mul_le_mul_of_nonneg_left (add_le_add hzW hyW) (by norm_num : (0 : ℝ) ≤ 4 / 3)).trans
    have hUq : 0 ≤ u / μ := by positivity
    have hWq : 0 ≤ w / μ := by positivity
    simp only [div_eq_mul_inv] at hUq hWq ⊢
    nlinarith only [hUq, hWq]

end BianchiIX
