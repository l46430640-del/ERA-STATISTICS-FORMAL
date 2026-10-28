import BianchiIX.Dynamics.ConnectionPhysicalReturn
import BianchiIX.Dynamics.ConnectionReturnAmplitudes
import BianchiIX.Algebra.ConnectionConeSize

noncomputable section

namespace BianchiIX

theorem connection_unit_phase_direction {p v : ConnectionParameters} (hμ : 4 ≤ p 0)
    (hv : ((p 0 + 1) / phaseNorm (p 0 + 1) 1) * v 0 = 1) : |v 0| ≤ 2 := by
  have H := phaseNorm_ratio_bounds (b := 1) (by linarith only [hμ] : 2 ≤ p 0 + 1) (by norm_num)
  have hR : 0 < (p 0 + 1) / phaseNorm (p 0 + 1) 1 := by linarith only [H.1]
  have hv0 : 0 ≤ v 0 := by nlinarith only [hv, hR]
  rw [abs_of_nonneg hv0]
  have HH := mul_le_mul_of_nonneg_right H.1 hv0
  nlinarith only [HH, hv]

/-- B.11 and B.12 applied to every unit physical-phase direction in the square-root cone. -/
theorem connectionReturn_cone_direction_bounds {p v : ConnectionParameters} {ε : ℝ}
    (hμ : 4 ≤ p 0) (hε : 0 ≤ ε ∧ ε ≤ 1 / 10000)
    (hu : 0 < p 1 ∧ p 1 ≤ ε / p 0) (hw : 0 < p 2 ∧ p 2 ≤ ε)
    (hv : ((p 0 + 1) / phaseNorm (p 0 + 1) 1) * v 0 = 1)
    (hvu : |v 1| ≤ Real.sqrt (p 1)) (hvw : |v 2| ≤ Real.sqrt (p 2)) :
    let L := -Real.log (p 2)
    let J := fderiv ℝ (connectionLogCoordinates ∘ connectionReturnState) p
    |fderiv ℝ connectionReturnPhaseError p v| ≤ 200000 * Real.sqrt ε / p 0 ∧
      |J v 1| ≤ 274 * L + 9000 * (1 / p 1 + L / p 0) * Real.sqrt (p 1) +
        32 * p 0 / p 2 * Real.sqrt (p 2) ∧
      |J v 2| ≤ 274 * L / p 0 ^ 2 + 9000 * (1 + L) / p 0 ^ 2 * Real.sqrt (p 1) +
        (1 + 32 / p 0) / p 2 * Real.sqrt (p 2) := by
  intro L J
  have hμ0 : 0 < p 0 := by linarith only [hμ]
  have hu' : 0 < p 1 ∧ p 1 ≤ (1 / 10000) / p 0 :=
    ⟨hu.1, hu.2.trans (div_le_div_of_nonneg_right hε.2 hμ0.le)⟩
  have hw' : 0 < p 2 ∧ p 2 ≤ 1 / 10000 := ⟨hw.1, hw.2.trans hε.2⟩
  have hv0 := connection_unit_phase_direction hμ hv
  have H := connectionReturn_phase_response_bounds_nonneg hμ ⟨hu'.1.le, hu'.2⟩ hw'
  have HA := connectionReturn_log_amplitude_bounds hμ hu' hw'
  have hphase := three_coordinate_linear_bound (fderiv ℝ connectionReturnPhaseError p) v
  have H0 := mul_le_mul hv0 H.1 (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
  have H1 := mul_le_mul hvu H.2.1 (abs_nonneg _) (Real.sqrt_nonneg _)
  have H2 := mul_le_mul hvw H.2.2 (abs_nonneg _) (Real.sqrt_nonneg _)
  have Hsize := connection_cone_phase_size hμ ⟨hε.1, by linarith only [hε.2]⟩ ⟨hu.1.le, hu.2⟩ ⟨hw.1.le, hw.2⟩
  have Hscaled := mul_le_mul_of_nonneg_left Hsize (show 0 ≤ 50000 / p 0 by positivity)
  have Hbound : |fderiv ℝ connectionReturnPhaseError p v| ≤
      (50000 / p 0) * (2 * (p 1 + p 2 ^ 2) / p 0 + Real.sqrt (p 1) +
        (p 1 + p 2) * Real.sqrt (p 2)) := by
    calc
      _ ≤ 2 * (50000 * (p 1 + p 2 ^ 2) / p 0 ^ 2) +
          Real.sqrt (p 1) * (50000 / p 0) + Real.sqrt (p 2) * (50000 * (p 1 + p 2) / p 0) :=
        hphase.trans (add_le_add (add_le_add H0 H1) H2)
      _ = _ := by ring
  refine ⟨?_, ?_, ?_⟩
  · exact (Hbound.trans Hscaled).trans_eq (by ring)
  · have Hb := three_coordinate_linear_bound
      ((ContinuousLinearMap.proj (1 : Fin 4) : (Fin 4 → ℝ) →L[ℝ] ℝ).comp J) v
    have Ha := mul_le_mul hv0 HA.1 (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
    have Hc := mul_le_mul hvu HA.2.2.1 (abs_nonneg _) (Real.sqrt_nonneg _)
    have Hd := mul_le_mul hvw HA.2.2.2.2.1 (abs_nonneg _) (Real.sqrt_nonneg _)
    change |J v 1| ≤ |v 0| * |J ![1, 0, 0] 1| + |v 1| * |J ![0, 1, 0] 1| + |v 2| * |J ![0, 0, 1] 1| at Hb
    exact (Hb.trans (add_le_add (add_le_add Ha Hc) Hd)).trans_eq (by ring)
  · have Hb := three_coordinate_linear_bound
      ((ContinuousLinearMap.proj (2 : Fin 4) : (Fin 4 → ℝ) →L[ℝ] ℝ).comp J) v
    have Ha := mul_le_mul hv0 HA.2.1 (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
    have Hc := mul_le_mul hvu HA.2.2.2.1 (abs_nonneg _) (Real.sqrt_nonneg _)
    have Hd := mul_le_mul hvw HA.2.2.2.2.2 (abs_nonneg _) (Real.sqrt_nonneg _)
    change |J v 2| ≤ |v 0| * |J ![1, 0, 0] 2| + |v 1| * |J ![0, 1, 0] 2| + |v 2| * |J ![0, 0, 1] 2| at Hb
    exact (Hb.trans (add_le_add (add_le_add Ha Hc) Hd)).trans_eq (by ring)

end BianchiIX
