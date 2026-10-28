import BianchiIX.Algebra.ConnectionBounds

noncomputable section

namespace BianchiIX

theorem connection_denom_upper {μ m u v w : ℝ} (hμ : 4 ≤ μ)
    (hm : |m - μ| ≤ 1 / 2) (hu : 0 ≤ u ∧ u ≤ 1 / 10000)
    (hv : 0 ≤ v ∧ v ≤ 1) (hw : 0 ≤ w ∧ w ≤ 1) :
    projectiveDenom (-m) u v w ≤ 2 * μ ^ 2 := by
  have hm0 : 0 ≤ m := by linarith only [(abs_le.mp hm).1, hμ]
  have hm2 : m ^ 2 ≤ (μ + 1 / 2) ^ 2 :=
    pow_le_pow_left₀ hm0 (by linarith only [(abs_le.mp hm).2]) 2
  have hu2 : u ^ 2 ≤ 1 := by
    have H := pow_le_pow_left₀ hu.1 hu.2 2
    norm_num at H
    linarith only [H]
  have hv2 : v ^ 2 ≤ 1 := by simpa using pow_le_pow_left₀ hv.1 hv.2 2
  have hw2 : w ^ 2 ≤ 1 := by simpa using pow_le_pow_left₀ hw.1 hw.2 2
  dsimp [projectiveDenom, curvature]
  nlinarith only [hm2, hu2, hv2, hw2, mul_nonneg hu.1 hv.1, mul_nonneg hv.1 hw.1,
    mul_nonneg hw.1 hu.1, sq_nonneg (μ - 4), hμ]

theorem connection_inverse_scale_lower {μ m u v w : ℝ} (hμ : 4 ≤ μ)
    (hm : |m - μ| ≤ 1 / 2) (hu : 0 ≤ u ∧ u ≤ 1 / 10000)
    (hv : 0 ≤ v ∧ v ≤ 1) (hw : 0 ≤ w ∧ w ≤ 1) :
    3 / μ ^ 2 ≤ 6 / projectiveDenom (-m) u v w := by
  have H := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 6)
    (connection_denom_bound hu hv hw).2 (connection_denom_upper hμ hm hu hv hw)
  convert! H using 1
  ring

theorem connection_original_clock_lower {μ m u v w : ℝ} (hμ : 4 ≤ μ)
    (hm : |m - μ| ≤ 1 / 2) (hu : 0 ≤ u ∧ u ≤ 1 / 10000)
    (hv : 0 ≤ v ∧ v ≤ 1) (hw : 0 ≤ w ∧ w ≤ 1) :
    1 / μ ≤ (6 / projectiveDenom (-m) u v w) * connectionSpeed m u v w := by
  have hμ0 : 0 < μ := by linarith only [hμ]
  have hscale := connection_inverse_scale_lower hμ hm hu hv hw
  have hD := (connection_speed_bounds hμ hm hu hv hw).1
  have H := mul_le_mul hscale hD (by positivity : 0 ≤ μ / 2)
    (div_nonneg (by norm_num) (connection_denom_bound hu hv hw).2.le)
  apply le_trans _ H
  apply (div_le_iff₀ hμ0).mpr
  field_simp
  norm_num

theorem connection_active_rate_neg {μ m u v w : ℝ} (hμ : 4 ≤ μ)
    (hm : |m - μ| ≤ 1 / 2) (hu : 0 ≤ u ∧ u ≤ 1 / 10000)
    (hv : 0 ≤ v ∧ v ≤ 1) (hw : 0 ≤ w ∧ w ≤ 1) :
    -m - 1 - coupling u v w < 0 := by
  have H := (connection_coupling_bounds hu.1 hv hw).1
  have hu2 := pow_le_pow_left₀ hu.1 hu.2 2
  nlinarith only [H, hu2, (abs_le.mp hm).1, hμ]

end BianchiIX
