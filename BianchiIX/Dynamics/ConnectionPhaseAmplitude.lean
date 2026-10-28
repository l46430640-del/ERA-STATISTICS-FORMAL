import BianchiIX.Dynamics.ConnectionConeDirections

noncomputable section

namespace BianchiIX

/-- The phase response retains the actual incoming amplitude rather than only its uniform threshold. -/
theorem connectionReturn_phase_cone_amplitude {p v : ConnectionParameters}
    (hμ : 4 ≤ p 0) (hu : 0 < p 1 ∧ p 1 ≤ (1 / 10000) / p 0)
    (hw : 0 < p 2 ∧ p 2 ≤ 1 / 10000)
    (hv : ((p 0 + 1) / phaseNorm (p 0 + 1) 1) * v 0 = 1)
    (hvu : |v 1| ≤ Real.sqrt (p 1)) (hvw : |v 2| ≤ Real.sqrt (p 2)) :
    |fderiv ℝ connectionReturnPhaseError p v| ≤ 150000 * Real.sqrt (p 1 + p 2) / p 0 := by
  have hμ0 : 0 < p 0 := by linarith only [hμ]
  have hu1 : p 1 ≤ 1 / 10000 := hu.2.trans (div_le_self (by norm_num) (by linarith only [hμ]))
  have hb : 0 ≤ p 1 + p 2 := add_nonneg hu.1.le hw.1.le
  have hb1 : p 1 + p 2 ≤ 1 := by linarith only [hu1, hw.2]
  have hw1 : p 2 ≤ 1 := by linarith only [hw.2]
  have hbs : p 1 + p 2 ≤ Real.sqrt (p 1 + p 2) := by
    have hs := Real.sqrt_le_one.mpr hb1
    nlinarith only [Real.sq_sqrt hb, Real.sqrt_nonneg (p 1 + p 2),
      mul_nonneg (Real.sqrt_nonneg (p 1 + p 2)) (sub_nonneg.mpr hs)]
  have hw2 : p 2 ^ 2 ≤ p 2 := by nlinarith only [hw.1.le, hw1]
  have hfirst : 2 * (p 1 + p 2 ^ 2) / p 0 ≤ Real.sqrt (p 1 + p 2) := by
    apply (div_le_iff₀ hμ0).mpr
    have H := mul_le_mul_of_nonneg_right hμ (Real.sqrt_nonneg (p 1 + p 2))
    nlinarith only [H, hw2, hbs, Real.sqrt_nonneg (p 1 + p 2)]
  have hsu : Real.sqrt (p 1) ≤ Real.sqrt (p 1 + p 2) :=
    Real.sqrt_le_sqrt (le_add_of_nonneg_right hw.1.le)
  have hsw : Real.sqrt (p 2) ≤ Real.sqrt (p 1 + p 2) :=
    Real.sqrt_le_sqrt (le_add_of_nonneg_left hu.1.le)
  have hlast : (p 1 + p 2) * Real.sqrt (p 2) ≤ Real.sqrt (p 1 + p 2) :=
    (mul_le_mul_of_nonneg_right hb1 (Real.sqrt_nonneg _)).trans (by simpa using hsw)
  have hsize : 2 * (p 1 + p 2 ^ 2) / p 0 + Real.sqrt (p 1) +
      (p 1 + p 2) * Real.sqrt (p 2) ≤ 3 * Real.sqrt (p 1 + p 2) := by
    linarith only [hfirst, hsu, hlast]
  have H := connectionReturn_phase_response_bounds_nonneg hμ ⟨hu.1.le, hu.2⟩ hw
  have H0 := mul_le_mul (connection_unit_phase_direction hμ hv) H.1 (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
  have H1 := mul_le_mul hvu H.2.1 (abs_nonneg _) (Real.sqrt_nonneg _)
  have H2 := mul_le_mul hvw H.2.2 (abs_nonneg _) (Real.sqrt_nonneg _)
  calc
    _ ≤ 2 * (50000 * (p 1 + p 2 ^ 2) / p 0 ^ 2) +
        Real.sqrt (p 1) * (50000 / p 0) + Real.sqrt (p 2) * (50000 * (p 1 + p 2) / p 0) :=
      (three_coordinate_linear_bound (fderiv ℝ connectionReturnPhaseError p) v).trans
        (add_le_add (add_le_add H0 H1) H2)
    _ = (50000 / p 0) * (2 * (p 1 + p 2 ^ 2) / p 0 + Real.sqrt (p 1) +
        (p 1 + p 2) * Real.sqrt (p 2)) := by ring
    _ ≤ (50000 / p 0) * (3 * Real.sqrt (p 1 + p 2)) :=
      mul_le_mul_of_nonneg_left hsize (by positivity)
    _ = _ := by ring

end BianchiIX
