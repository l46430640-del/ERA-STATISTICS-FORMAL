import BianchiIX.Dynamics.ConnectionReturnResponse
import BianchiIX.Analysis.ConnectionReturnBounds

noncomputable section

namespace BianchiIX

/-- All six ordinary parameter derivatives of the positive-wall first-return log amplitudes. -/
theorem connectionReturn_log_amplitude_bounds {p : ConnectionParameters} (hμ : 4 ≤ p 0)
    (hu : 0 < p 1 ∧ p 1 ≤ (1 / 10000) / p 0) (hw : 0 < p 2 ∧ p 2 ≤ 1 / 10000) :
    let μ := p 0
    let u := p 1
    let w := p 2
    let L := -Real.log w
    let J := fderiv ℝ (connectionLogCoordinates ∘ connectionReturnState) p
    |J ![1, 0, 0] 1| ≤ 137 * L ∧
    |J ![1, 0, 0] 2| ≤ 137 * L / μ ^ 2 ∧
    |J ![0, 1, 0] 1| ≤ 9000 * (1 / u + L / μ) ∧
    |J ![0, 1, 0] 2| ≤ 9000 * (1 + L) / μ ^ 2 ∧
    |J ![0, 0, 1] 1| ≤ 32 * μ / w ∧
    |J ![0, 0, 1] 2| ≤ (1 + 32 / μ) / w := by
  intro μ u w L J
  let y := connectionEntry μ u w
  let D := connectionLogFlowVariation y 0 (connectionReturnTime p)
  have hμ0 : 0 < μ := by linarith only [hμ]
  have hu0 : 0 < u := hu.1
  have hw0 : 0 < w := hw.1
  have hL : 0 ≤ L := neg_nonneg.mpr (Real.log_nonpos hw0.le (by linarith only [hw.2]))
  have hu1 : u ≤ 1 := by
    have H := (le_div_iff₀ hμ0).mp hu.2
    nlinarith only [H, hμ, hu0]
  have hμ1 : 1 ≤ μ := by linarith only [hμ]
  have hrad : J ![1, 0, 0] = D ![-1, 0, 0, 0] := by
    simpa [J, D, y, μ, u, w] using connectionReturn_log_differential hμ hu hw ![1, 0, 0]
  have hstrong : J ![0, 1, 0] = D ![0, 1, 0, 0] := by
    simpa [J, D, y, μ, u, w] using connectionReturn_log_differential hμ hu hw ![0, 1, 0]
  have hgrowing : J ![0, 0, 1] = D ![0, 0, 0, 1] - (1 / w) • connectionLogCoordinateRates (connectionReturnState p) := by
    simpa [J, D, y, μ, u, w] using connectionReturn_log_differential hμ hu hw ![0, 0, 1]
  have H := connectionReturn_fixed_clock_bounds hμ hu hw
  have hradial : |D ![-1, 0, 0, 0] 1| ≤ (2048 / 15) * L ∧
      |D ![-1, 0, 0, 0] 2| ≤ ((2048 / 15) * L) / μ ^ 2 := by
    have Hn : ‖connectionWeightedTangent μ (D ![-1, 0, 0, 0]) - ![(0 : ℝ), 0]‖ ≤ (2048 / 15) * L := by
      have hz : (![(0 : ℝ), 0] : Fin 2 → ℝ) = 0 := by ext i; fin_cases i <;> rfl
      conv_lhs => arg 1; arg 2; rw [hz]
      rw [sub_zero]
      exact H.1.2.2
    simpa using connectionShiftedTangent_component_bounds hμ0 Hn
  have hcoeff := connection_growing_endpoint_coefficients hμ ⟨hu.1.le, hu.2⟩ hw (mul_neg_log_le_one hw0)
  have hg1 : |D ![0, 0, 0, 1] 1| ≤ 16 * μ / w := H.2.2.2.1.trans hcoeff.1
  have hg2 : |D ![0, 0, 0, 1] 2| ≤ 200 / (μ ^ 3 * w) := H.2.2.2.2.trans hcoeff.2
  have hc := connectionReturn_control hμ ⟨hu.1.le, hu.2⟩ hw
  have hr := (hc.2 (connectionReturnTime p) ⟨hc.1.le, le_rfl⟩).2
  change connectionRegion μ (connectionReturnState p) at hr
  have ha : |connectionLogCoordinateRates (connectionReturnState p) 1| ≤ 2 * μ :=
    (connection_amplitude_base_bounds hμ hr.1 hr.2.1 hr.2.2.1 hr.2.2.2).2.1
  have hb : |connectionLogCoordinateRates (connectionReturnState p) 2| ≤ 1 + 8 / μ :=
    connection_weak_clock_rate_bound hμ hr.1 hr.2.1 hr.2.2.1 hr.2.2.2
  have hcorrection (i : Fin 4) : |J ![0, 0, 1] i| ≤
      |D ![0, 0, 0, 1] i| + |connectionLogCoordinateRates (connectionReturnState p) i| / w := by
    rw [hgrowing]
    have Habs := abs_sub (D ![0, 0, 0, 1] i) ((1 / w) * connectionLogCoordinateRates (connectionReturnState p) i)
    simpa [abs_mul, abs_of_pos hw0, div_eq_mul_inv, mul_comm] using Habs
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hrad]
    exact hradial.1.trans (by nlinarith only [hL])
  · rw [hrad]
    exact hradial.2.trans (div_le_div_of_nonneg_right (by nlinarith only [hL]) (sq_nonneg μ))
  · rw [hstrong]
    apply H.2.1.2.1.trans
    change 1 / u + 256 + 8960 * L / μ ≤ 9000 * (1 / u + L / μ)
    have hi : 1 ≤ 1 / u := (le_div_iff₀ hu0).mpr (by simpa using hu1)
    have hq : 0 ≤ L / μ := div_nonneg hL hμ0.le
    simp only [div_eq_mul_inv] at hi hq ⊢
    nlinarith only [hi, hq]
  · rw [hstrong]
    apply H.2.1.2.2.trans
    apply div_le_div_of_nonneg_right _ (sq_nonneg μ)
    have hq : L / μ ≤ L := (div_le_iff₀ hμ0).mpr (by nlinarith only [hμ1, hL])
    change 256 + 8960 * L / μ ≤ 9000 * (1 + L)
    simp only [div_eq_mul_inv] at hq ⊢
    nlinarith only [hq, hL]
  · apply (hcorrection 1).trans
    apply (add_le_add hg1 (div_le_div_of_nonneg_right ha hw0.le)).trans
    change 16 * μ / w + 2 * μ / w ≤ 32 * μ / w
    have hq : 0 ≤ μ / w := (div_pos hμ0 hw0).le
    simp only [div_eq_mul_inv] at hq ⊢
    nlinarith only [hq]
  · apply (hcorrection 2).trans
    apply (add_le_add hg2 (div_le_div_of_nonneg_right hb hw0.le)).trans
    have hsmall : 200 / μ ^ 3 ≤ 24 / μ := by
      calc
        200 / μ ^ 3 = (200 / μ ^ 2) / μ := by ring
        _ ≤ 24 / μ := div_le_div_of_nonneg_right
          ((div_le_iff₀ (sq_pos_of_pos hμ0)).mpr (by nlinarith only [hμ])) hμ0.le
    calc
      200 / (μ ^ 3 * w) + (1 + 8 / μ) / w = (1 + 8 / μ + 200 / μ ^ 3) / w := by ring
      _ ≤ (1 + 32 / μ) / w := div_le_div_of_nonneg_right (by
        simp only [div_eq_mul_inv] at hsmall ⊢
        linarith only [hsmall]) hw0.le

end BianchiIX
