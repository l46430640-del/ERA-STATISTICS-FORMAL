import BianchiIX.Algebra.MatchingPhaseBounds

noncomputable section

namespace BianchiIX

theorem phaseNorm_defect_bounds {μ a b : ℝ} (hμ : 0 < μ) (ha : μ / 2 ≤ a) :
    0 ≤ phaseNorm a b - a ∧ phaseNorm a b - a ≤ b ^ 2 / μ := by
  have ha0 : 0 < a := lt_of_lt_of_le (by positivity) ha
  have hnorm := phaseNorm_ge (b := b) ha0.le
  refine ⟨sub_nonneg.mpr hnorm, ?_⟩
  rw [phaseNorm_defect ha0]
  exact div_le_div_of_nonneg_left (sq_nonneg b) hμ (by linarith only [ha, hnorm])

/-- Endpoint defects convert the matching-phase drift to the two physical core phases. -/
theorem matchingPhase_endpoint_bound {μ m u v w : ℝ} (hμ : 4 ≤ μ) (hm : |m - μ| ≤ 1 / 2)
    (hu : 0 ≤ u) (hv : 0 ≤ v ∧ v ≤ w)
    (hJ : |matchingPhase m v 1 - matchingPhase μ 1 w| ≤ 20 * u / μ + w ^ 2 / μ ^ 2) :
    |phaseNorm (m - 1) 1 - phaseNorm (μ + 1) 1 + 2| ≤ 24 * (u + w ^ 2) / μ := by
  have hμ0 : 0 < μ := by linarith only [hμ]
  have he0 := phaseNorm_defect_bounds (b := w) hμ0 (show μ / 2 ≤ μ - 1 by linarith only [hμ])
  have he1 := phaseNorm_defect_bounds (b := v) hμ0
    (show μ / 2 ≤ m + 1 by linarith only [hμ, (abs_le.mp hm).1])
  have hv2 := pow_le_pow_left₀ hv.1 hv.2 2
  have he1' := he1.2.trans (div_le_div_of_nonneg_right hv2 hμ0.le)
  have hid : phaseNorm (m - 1) 1 - phaseNorm (μ + 1) 1 + 2 =
      matchingPhase m v 1 - matchingPhase μ 1 w +
        (phaseNorm (μ - 1) w - (μ - 1)) - (phaseNorm (m + 1) v - (m + 1)) := by
    dsimp [matchingPhase]
    ring
  rw [hid]
  have H := (abs_sub (matchingPhase m v 1 - matchingPhase μ 1 w + (phaseNorm (μ - 1) w - (μ - 1)))
    (phaseNorm (m + 1) v - (m + 1))).trans (add_le_add (abs_add_le _ _) le_rfl)
  rw [abs_of_nonneg he0.1, abs_of_nonneg he1.1] at H
  apply (H.trans (add_le_add (add_le_add hJ he0.2) he1')).trans
  have hμsq : μ ≤ μ ^ 2 := by nlinarith only [hμ, sq_nonneg (μ - 1)]
  have hsq := div_le_div_of_nonneg_left (sq_nonneg w) hμ0 hμsq
  have huq := div_nonneg hu hμ0.le
  have hwq := div_nonneg (sq_nonneg w) hμ0.le
  calc
    20 * u / μ + w ^ 2 / μ ^ 2 + w ^ 2 / μ + w ^ 2 / μ ≤
        20 * (u / μ) + 3 * (w ^ 2 / μ) := by
      calc
        _ ≤ 20 * u / μ + w ^ 2 / μ + w ^ 2 / μ + w ^ 2 / μ := by gcongr
        _ = _ := by ring
    _ ≤ 24 * (u / μ) + 24 * (w ^ 2 / μ) := by nlinarith only [huq, hwq]
    _ = 24 * (u + w ^ 2) / μ := by ring

end BianchiIX
