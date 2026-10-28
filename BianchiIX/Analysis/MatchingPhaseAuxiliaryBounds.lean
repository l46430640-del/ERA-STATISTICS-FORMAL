import BianchiIX.Analysis.MatchingPhaseWeightDifferential

noncomputable section

namespace BianchiIX

theorem matchingPhase_auxiliary_m_bounds {μ m v w : ℝ} (hμ : 4 ≤ μ) (hm : |m - μ| ≤ 1 / 2) :
    0 ≤ matchingPhaseSlopeDm m v w ∧
    matchingPhaseSlopeDm m v w ≤ 9 * (v ^ 2 + w ^ 2) / (2 * μ ^ 3) ∧
    |matchingPhaseWeightDm m v w - 1| ≤ 3 * (v ^ 2 + w ^ 2) / μ ^ 2 := by
  have hμ0 : 0 < μ := by linarith only [hμ]
  have hμne := ne_of_gt hμ0
  have ha0 : 0 < m + 1 := by linarith only [hμ, (abs_le.mp hm).1]
  have hb0 : 0 < m - 1 := by linarith only [hμ, (abs_le.mp hm).1]
  have hp0 := phaseNorm_pos (b := v) ha0
  have hn0 := phaseNorm_pos (b := w) hb0
  have wall (a b : ℝ) (ha : 5 * μ / 8 ≤ a) :
      0 ≤ phaseNormKernel a b ∧ phaseNormKernel a b ≤ 3 / (2 * μ ^ 2) ∧
        b ^ 2 / phaseNorm a b ^ 3 ≤ 9 * b ^ 2 / (2 * μ ^ 3) := by
    have ha0' : 0 < a := by linarith only [ha, hμ0]
    have hK := phaseNorm_pos (b := b) ha0'
    have H := phaseNormKernel_derivative_bounds (b := b) (by positivity : 0 < 5 * μ / 8) ha
    refine ⟨H.1, H.2.1.trans ?_, ?_⟩
    · convert! div_le_div_of_nonneg_right (show (32 / 25 : ℝ) ≤ 3 / 2 by norm_num) (sq_nonneg μ) using 1 <;> ring
    · have Hcube : 1 / phaseNorm a b ^ 3 ≤ 9 / (2 * μ ^ 3) := by
        have Hda := H.2.2.1
        rw [phaseNormKernelDa, abs_div, abs_neg, abs_one, abs_of_pos (pow_pos hK 3)] at Hda
        apply Hda.trans
        convert! div_le_div_of_nonneg_right (show (512 / 125 : ℝ) ≤ 9 / 2 by norm_num)
          (by positivity : 0 ≤ μ ^ 3) using 1 <;> ring
      convert! mul_le_mul_of_nonneg_left Hcube (sq_nonneg b) using 1 <;> ring
  have hp := wall (m + 1) v (by linarith only [hμ, (abs_le.mp hm).1])
  have hn := wall (m - 1) w (by linarith only [hμ, (abs_le.mp hm).1])
  have hqpos : 0 ≤ v ^ 2 / phaseNorm (m + 1) v ^ 3 := by positivity
  have hrpos : 0 ≤ w ^ 2 / phaseNorm (m - 1) w ^ 3 := by positivity
  have hfm : matchingPhaseSlopeDm m v w ≤ 9 * (v ^ 2 + w ^ 2) / (2 * μ ^ 3) :=
    (add_le_add hp.2.2 hn.2.2).trans_eq (by ring)
  have hf : |matchingPhaseSlope m v w - 1| ≤ 3 * (v ^ 2 + w ^ 2) / (2 * μ ^ 2) := by
    have hpR := phaseNorm_ratio_defect (b := v) ha0
    have hnR := phaseNorm_ratio_defect (b := w) hb0
    have hid : matchingPhaseSlope m v w - 1 =
        -(v ^ 2 * phaseNormKernel (m + 1) v + w ^ 2 * phaseNormKernel (m - 1) w) := by
      dsimp [matchingPhaseSlope]
      linarith only [hpR, hnR]
    rw [hid, abs_neg, abs_of_nonneg (add_nonneg (mul_nonneg (sq_nonneg v) hp.1) (mul_nonneg (sq_nonneg w) hn.1))]
    exact (add_le_add (mul_le_mul_of_nonneg_left hp.2.1 (sq_nonneg v))
      (mul_le_mul_of_nonneg_left hn.2.1 (sq_nonneg w))).trans_eq (by ring)
  refine ⟨add_nonneg hqpos hrpos, hfm, ?_⟩
  have hid : matchingPhaseWeightDm m v w - 1 =
      (matchingPhaseSlope m v w - 1) - v ^ 2 / phaseNorm (m + 1) v ^ 3 + w ^ 2 / phaseNorm (m - 1) w ^ 3 := by
    dsimp [matchingPhaseWeightDm]
    ring
  rw [hid]
  have H := (abs_add_le (matchingPhaseSlope m v w - 1 - v ^ 2 / phaseNorm (m + 1) v ^ 3)
    (w ^ 2 / phaseNorm (m - 1) w ^ 3)).trans
      (add_le_add (abs_sub (matchingPhaseSlope m v w - 1) (v ^ 2 / phaseNorm (m + 1) v ^ 3)) le_rfl)
  rw [abs_of_nonneg hqpos, abs_of_nonneg hrpos] at H
  calc
    _ ≤ |matchingPhaseSlope m v w - 1| + matchingPhaseSlopeDm m v w := H.trans_eq (by dsimp [matchingPhaseSlopeDm]; ring)
    _ ≤ 3 * (v ^ 2 + w ^ 2) / (2 * μ ^ 2) + 9 * (v ^ 2 + w ^ 2) / (2 * μ ^ 3) := add_le_add hf hfm
    _ = (3 * μ + 9) * (v ^ 2 + w ^ 2) / (2 * μ ^ 3) := by field_simp
    _ ≤ 6 * μ * (v ^ 2 + w ^ 2) / (2 * μ ^ 3) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_right (by linarith only [hμ]) (by positivity)
    _ = 3 * (v ^ 2 + w ^ 2) / μ ^ 2 := by field_simp; ring

theorem connectionPhaseRemainder_phase_bound {μ m u v w : ℝ} (hμ : 4 ≤ μ)
    (hm : |m - μ| ≤ 1 / 2) (hu : 0 ≤ u ∧ u ≤ 1 / 10000)
    (hv : 0 ≤ v ∧ v ≤ 1) (hw : 0 ≤ w ∧ w ≤ 1) :
    |connectionPhaseRemainderDm m u v w / matchingPhaseSlope m v w| ≤ 20 / μ ^ 2 := by
  have hμ0 : 0 < μ := by linarith only [hμ]
  have hμne := ne_of_gt hμ0
  have haux := matchingPhase_auxiliary_m_bounds (v := v) (w := w) hμ hm
  have hvar := (matchingPhase_inverse_weighted_bounds hμ hm hv hw).1
  have hd : |v - w| ≤ 1 := abs_le.mpr ⟨by linarith only [hv.1, hw.2], by linarith only [hv.2, hw.1]⟩
  have hS : |v + w - u| ≤ 2 := by
    apply abs_le.mpr
    constructor <;> linarith only [hv.1, hv.2, hw.1, hw.2, hu.1, hu.2]
  have hv2 : v ^ 2 ≤ 1 := by simpa using pow_le_pow_left₀ hv.1 hv.2 2
  have hw2 : w ^ 2 ≤ 1 := by simpa using pow_le_pow_left₀ hw.1 hw.2 2
  have H1 : |matchingPhaseSlopeDm m v w * (v - w)| ≤ 9 * (v ^ 2 + w ^ 2) / (2 * μ ^ 3) := by
    rw [abs_mul, abs_of_nonneg haux.1]
    exact (mul_le_mul haux.2.1 hd (abs_nonneg _) (by positivity)).trans_eq (by ring)
  have H2 : |(v + w - u) * (matchingPhaseWeightDm m v w - 1)| ≤ 6 * (v ^ 2 + w ^ 2) / μ ^ 2 := by
    rw [abs_mul]
    exact (mul_le_mul hS haux.2.2 (abs_nonneg _) (by norm_num)).trans_eq (by ring)
  have HN := (abs_add_le _ _).trans (add_le_add H1 H2)
  change |connectionPhaseRemainderDm m u v w| ≤ _ at HN
  rw [div_eq_mul_inv, abs_mul]
  calc
    _ ≤ (9 * (v ^ 2 + w ^ 2) / (2 * μ ^ 3) + 6 * (v ^ 2 + w ^ 2) / μ ^ 2) * (4 / 3) :=
      mul_le_mul HN (by simpa only [one_div] using hvar) (abs_nonneg _) (by positivity)
    _ = (6 / μ ^ 3 + 8 / μ ^ 2) * (v ^ 2 + w ^ 2) := by ring
    _ ≤ (6 / μ ^ 3 + 8 / μ ^ 2) * 2 :=
      mul_le_mul_of_nonneg_left (by linarith only [hv2, hw2]) (by positivity)
    _ = (12 + 16 * μ) / μ ^ 3 := by field_simp; ring
    _ ≤ (20 * μ) / μ ^ 3 := div_le_div_of_nonneg_right (by linarith only [hμ]) (by positivity)
    _ = 20 / μ ^ 2 := by field_simp

end BianchiIX
