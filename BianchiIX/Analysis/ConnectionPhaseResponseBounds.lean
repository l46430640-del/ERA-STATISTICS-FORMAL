import BianchiIX.Analysis.ConnectionPhaseEndpointFactor
import BianchiIX.Analysis.ConnectionFeedbackBounds

noncomputable section

namespace BianchiIX

theorem connectionExitPhase_response_bound {μ m v : ℝ} (hμ : 4 ≤ μ)
    (hm : |m - μ| ≤ 1 / 2) (hv : 0 ≤ v ∧ v ≤ 1) (Z Y : ℝ) :
    |connectionExitPhaseFactor m v * (Z - (v ^ 2 / phaseNorm (m + 1) v) * Y)| ≤
      (4 / 3) * (|Z| + (v ^ 2 / μ) * |Y|) := by
  obtain ⟨hA0, hA, _, hQ0, hQ⟩ := connectionExitPhaseFactor_bounds hμ hm hv
  rw [abs_mul, abs_of_nonneg hA0]
  apply (mul_le_mul_of_nonneg_left (abs_sub _ _) hA0).trans
  rw [abs_mul, abs_of_nonneg hQ0]
  exact mul_le_mul hA (add_le_add le_rfl (mul_le_mul_of_nonneg_right hQ (abs_nonneg Y)))
    (by positivity) (by norm_num)

theorem connectionExitPhase_radial_error_bound {μ m v w : ℝ} (hμ : 4 ≤ μ)
    (hm : |m - μ| ≤ 1 / 2) (hv : 0 ≤ v ∧ v ≤ 1) (Z Y : ℝ) :
    |connectionExitPhaseFactor m v * (Z - (v ^ 2 / phaseNorm (m + 1) v) * Y) -
      (μ + 1) / phaseNorm (μ + 1) 1| ≤
    |Z - matchingPhaseSlope μ 1 w| + (4 * v ^ 2 / μ ^ 2) * |Z| +
      (4 / 3) * ((v ^ 2 / μ) * |Y|) + 2 * w ^ 2 / μ ^ 2 := by
  obtain ⟨hA0, hA, hAd, hQ0, hQ⟩ := connectionExitPhaseFactor_bounds hμ hm hv
  let A := connectionExitPhaseFactor m v
  let Q := v ^ 2 / phaseNorm (m + 1) v
  let F := matchingPhaseSlope μ 1 w
  let R := (μ + 1) / phaseNorm (μ + 1) 1
  have hid : A * (Z - Q * Y) - R = (Z - F) + (A - 1) * Z - A * (Q * Y) + (F - R) := by ring
  change |A * (Z - Q * Y) - R| ≤ _
  rw [hid]
  have H := (abs_add_le ((Z - F) + (A - 1) * Z - A * (Q * Y)) (F - R)).trans
    (add_le_add ((abs_sub ((Z - F) + (A - 1) * Z) (A * (Q * Y))).trans
      (add_le_add (abs_add_le (Z - F) ((A - 1) * Z)) le_rfl)) le_rfl)
  have Hb : |A * (Q * Y)| ≤ (4 / 3) * ((v ^ 2 / μ) * |Y|) := by
    rw [abs_mul, abs_mul, abs_of_nonneg hA0, abs_of_nonneg hQ0]
    exact mul_le_mul hA (mul_le_mul_of_nonneg_right hQ (abs_nonneg Y)) (by positivity) (by norm_num)
  have Ha : |(A - 1) * Z| ≤ (4 * v ^ 2 / μ ^ 2) * |Z| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right hAd (abs_nonneg Z)
  have He : |F - R| ≤ 2 * w ^ 2 / μ ^ 2 := matchingPhase_entry_slope_defect hμ
  exact H.trans (add_le_add (add_le_add (add_le_add le_rfl Ha) Hb) He)

theorem connectionPhaseFeedbackBudget_scale {μ u w : ℝ} (hμ : 4 ≤ μ) (hu : 0 ≤ u) :
    (16 / 15) * connectionPhaseFeedbackBudget μ u w ≤ 35000 * (u + w ^ 2) / μ ^ 2 := by
  have hμ0 : 0 < μ := by linarith only [hμ]
  have hU : u / μ ^ 3 ≤ (u / μ ^ 2) / 4 := by
    calc
      u / μ ^ 3 = (u / μ ^ 2) / μ := by ring
      _ ≤ (u / μ ^ 2) / 4 := div_le_div_of_nonneg_left (by positivity) (by norm_num) hμ
  have hW : w ^ 2 / μ ^ 3 ≤ (w ^ 2 / μ ^ 2) / 4 := by
    calc
      w ^ 2 / μ ^ 3 = (w ^ 2 / μ ^ 2) / μ := by ring
      _ ≤ (w ^ 2 / μ ^ 2) / 4 := div_le_div_of_nonneg_left (by positivity) (by norm_num) hμ
  have hU0 : 0 ≤ u / μ ^ 2 := by positivity
  have hW0 : 0 ≤ w ^ 2 / μ ^ 2 := by positivity
  have hid : connectionPhaseFeedbackBudget μ u w =
      128 * (u / μ ^ 3) + 32768 * (u / μ ^ 2) + 528 * (w ^ 2 / μ ^ 3) := by
    unfold connectionPhaseFeedbackBudget
    ring
  rw [hid]
  simp only [div_eq_mul_inv] at hU hW hU0 hW0 ⊢
  nlinarith only [hU, hW, hU0, hW0]

theorem connection_endpoint_weighted_log_bound {μ v w L C Y : ℝ} (hμ : 0 < μ) (hC : 0 ≤ C)
    (hweight : (1 + L) * v ^ 2 ≤ μ * w ^ 2) (hY : |Y| ≤ C * (1 + L) / μ ^ 2) :
    (v ^ 2 / μ) * |Y| ≤ C * w ^ 2 / μ ^ 2 := by
  calc
    (v ^ 2 / μ) * |Y| ≤ (v ^ 2 / μ) * (C * (1 + L) / μ ^ 2) :=
      mul_le_mul_of_nonneg_left hY (by positivity)
    _ = C * ((1 + L) * v ^ 2) / μ ^ 3 := by ring
    _ ≤ C * (μ * w ^ 2) / μ ^ 3 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hweight hC) (by positivity)
    _ = C * w ^ 2 / μ ^ 2 := by field_simp

end BianchiIX
