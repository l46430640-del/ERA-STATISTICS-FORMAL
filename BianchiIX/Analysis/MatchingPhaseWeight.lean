import BianchiIX.Analysis.ConnectionPhaseKernelBounds

noncomputable section

namespace BianchiIX

theorem matchingPhaseWeight_identity {m v w : ℝ} (hm : 1 < m) :
    matchingPhaseWeight m v w = matchingPhase m v w - (m + 1) / phaseNorm (m + 1) v +
      (m - 1) / phaseNorm (m - 1) w := by
  have hp := phaseNorm_pos (b := v) (show 0 < m + 1 by linarith only [hm])
  have hn := phaseNorm_pos (b := w) (show 0 < m - 1 by linarith only [hm])
  dsimp [matchingPhaseWeight, matchingPhaseSlope, matchingPhase]
  field_simp
  linear_combination -phaseNorm (m - 1) w * phaseNorm_sq (m + 1) v -
    phaseNorm (m + 1) v * phaseNorm_sq (m - 1) w

theorem matchingPhaseWeight_offset {m v w : ℝ} (hm : 1 < m) :
    matchingPhaseWeight m v w - m =
      v ^ 2 * (phaseNorm (m + 1) v + 1) /
        (phaseNorm (m + 1) v * (phaseNorm (m + 1) v + m + 1)) +
      w ^ 2 * (phaseNorm (m - 1) w - 1) /
        (phaseNorm (m - 1) w * (phaseNorm (m - 1) w + m - 1)) := by
  have hp : 0 < m + 1 := by linarith only [hm]
  have hn : 0 < m - 1 := by linarith only [hm]
  rw [matchingPhaseWeight_identity hm]
  calc
    _ = (phaseNorm (m + 1) v - (m + 1)) + (phaseNorm (m - 1) w - (m - 1)) +
        (1 - (m + 1) / phaseNorm (m + 1) v) - (1 - (m - 1) / phaseNorm (m - 1) w) := by
      dsimp [matchingPhase]
      ring
    _ = _ := by
      rw [phaseNorm_defect hp, phaseNorm_defect hn, phaseNorm_ratio_defect hp, phaseNorm_ratio_defect hn]
      have hkp := phaseNorm_pos (b := v) hp
      have hkn := phaseNorm_pos (b := w) hn
      have hsp : 0 < phaseNorm (m + 1) v + m + 1 := by linarith only [hkp, hp]
      have hsn : 0 < phaseNorm (m - 1) w + m - 1 := by linarith only [hkn, hn]
      dsimp [phaseNormKernel]
      field_simp
      ring

theorem matchingPhaseWeight_offset_bounds {μ m v w : ℝ} (hμ : 4 ≤ μ) (hm : |m - μ| ≤ 1 / 2) :
    0 ≤ matchingPhaseWeight m v w - m ∧
      matchingPhaseWeight m v w - m ≤ 8 * (v ^ 2 + w ^ 2) / (5 * μ) := by
  have hμ0 : 0 < μ := by linarith only [hμ]
  have hm1 : 1 < m := by linarith only [hμ, (abs_le.mp hm).1]
  have hp := phaseNorm_ge (b := v) (show 0 ≤ m + 1 by linarith only [hm1])
  have hn := phaseNorm_ge (b := w) (show 0 ≤ m - 1 by linarith only [hm1])
  have term (K a r e l : ℝ) (hl : 0 < l) (hK : l ≤ K) (ha : 0 < a)
      (he0 : 0 ≤ K + e) (he : e ≤ a) :
      0 ≤ r ^ 2 * (K + e) / (K * (K + a)) ∧
        r ^ 2 * (K + e) / (K * (K + a)) ≤ r ^ 2 / l := by
    have hK0 := hl.trans_le hK
    have hS : 0 < K + a := add_pos hK0 ha
    refine ⟨by positivity, ?_⟩
    calc
      _ ≤ r ^ 2 * (K + a) / (K * (K + a)) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left (by linarith only [he]) (sq_nonneg r)
      _ = r ^ 2 / K := by field_simp
      _ ≤ r ^ 2 / l := div_le_div_of_nonneg_left (sq_nonneg r) hl hK
  have hpterm := term (phaseNorm (m + 1) v) (m + 1) v 1 μ hμ0
    (by linarith only [hp, (abs_le.mp hm).1]) (by linarith only [hm1])
    (by linarith only [hp, hm1]) (by linarith only [hm1])
  have hnterm := term (phaseNorm (m - 1) w) (m - 1) w (-1) (5 * μ / 8) (by positivity)
    (by linarith only [hn, hμ, (abs_le.mp hm).1]) (by linarith only [hm1])
    (by linarith only [hn, hμ, (abs_le.mp hm).1]) (by linarith only [hm1])
  have hid := matchingPhaseWeight_offset (v := v) (w := w) hm1
  have hid' : matchingPhaseWeight m v w - m =
      v ^ 2 * (phaseNorm (m + 1) v + 1) / (phaseNorm (m + 1) v * (phaseNorm (m + 1) v + (m + 1))) +
      w ^ 2 * (phaseNorm (m - 1) w + -1) / (phaseNorm (m - 1) w * (phaseNorm (m - 1) w + (m - 1))) := by
    convert! hid using 1
    ring
  rw [hid']
  refine ⟨add_nonneg hpterm.1 hnterm.1, (add_le_add hpterm.2 hnterm.2).trans ?_⟩
  have H := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ 8 / 5 by norm_num) (sq_nonneg v)) hμ0.le
  convert! add_le_add H (le_refl (w ^ 2 / (5 * μ / 8))) using 1 <;> ring

theorem matchingPhaseWeight_sharp_bounds {μ m v w : ℝ} (hμ : 4 ≤ μ) (hm : |m - μ| ≤ 1 / 2)
    (hv : 0 ≤ v ∧ v ≤ 1) (hw : 0 ≤ w ∧ w ≤ 1) :
    0 < matchingPhaseWeight m v w ∧ matchingPhaseWeight m v w ≤ 3 * μ / 2 ∧
      matchingPhaseWeight m v w - m ≤ 4 / 5 := by
  have hμ0 : 0 < μ := by linarith only [hμ]
  have H := matchingPhaseWeight_offset_bounds (v := v) (w := w) hμ hm
  have hv2 : v ^ 2 ≤ 1 := by simpa using pow_le_pow_left₀ hv.1 hv.2 2
  have hw2 : w ^ 2 ≤ 1 := by simpa using pow_le_pow_left₀ hw.1 hw.2 2
  have hsmall : matchingPhaseWeight m v w - m ≤ 4 / 5 := H.2.trans
    ((div_le_iff₀ (by positivity : 0 < 5 * μ)).mpr (by nlinarith only [hv2, hw2, hμ]))
  refine ⟨?_, ?_, hsmall⟩
  · linarith only [H.1, hμ, (abs_le.mp hm).1]
  · linarith only [hsmall, hμ, (abs_le.mp hm).2]

theorem matchingPhaseWeight_speed_offset_bounds {μ m u v w : ℝ} (hμ : 4 ≤ μ)
    (hm : |m - μ| ≤ 1 / 2) (hu : 0 ≤ u ∧ u ≤ 1 / 10000)
    (hv : 0 ≤ v ∧ v ≤ 1) (hw : 0 ≤ w ∧ w ≤ 1) :
    0 ≤ matchingPhaseWeight m v w - connectionSpeed m u v w ∧
      |matchingPhaseWeight m v w - connectionSpeed m u v w| ≤ 2 := by
  have Hoff := matchingPhaseWeight_offset_bounds (v := v) (w := w) hμ hm
  have Hsmall := (matchingPhaseWeight_sharp_bounds hμ hm hv hw).2.2
  have HC := connection_coupling_bounds hu.1 hv hw
  have hu2 := pow_le_pow_left₀ hu.1 hu.2 2
  have hlow : 0 ≤ matchingPhaseWeight m v w - connectionSpeed m u v w := by
    dsimp [connectionSpeed]
    nlinarith only [Hoff.1, HC.1, hu2]
  refine ⟨hlow, ?_⟩
  rw [abs_of_nonneg hlow]
  dsimp [connectionSpeed]
  linarith only [Hsmall, HC.2, hu.2]

def connectionPhaseRemainder (m u v w : ℝ) : ℝ :=
  matchingPhaseSlope m v w * (v - w) + (v + w - u) *
    (matchingPhaseWeight m v w - connectionSpeed m u v w)

theorem connectionPhaseA_remainder {m u v w : ℝ} (hD : connectionSpeed m u v w ≠ 0) :
    connectionPhaseA m u v w = -(v + w - u) - connectionPhaseRemainder m u v w / connectionSpeed m u v w := by
  dsimp [connectionPhaseA, connectionPhaseRemainder]
  field_simp
  ring

theorem connectionPhaseRemainder_bound {μ m u v w : ℝ} (hμ : 4 ≤ μ)
    (hm : |m - μ| ≤ 1 / 2) (hu : 0 ≤ u ∧ u ≤ 1 / 10000)
    (hv : 0 ≤ v ∧ v ≤ 1) (hw : 0 ≤ w ∧ w ≤ 1) :
    |connectionPhaseRemainder m u v w| ≤ 6 := by
  have hf := matchingPhase_slope_bounds hμ hm hv hw
  have hf0 : 0 ≤ matchingPhaseSlope m v w := by linarith only [hf.1]
  have hd : |v - w| ≤ 1 := abs_le.mpr ⟨by linarith only [hv.1, hw.2], by linarith only [hv.2, hw.1]⟩
  have hS : |v + w - u| ≤ 5 / 2 := by
    apply abs_le.mpr
    constructor <;> linarith only [hv.1, hv.2, hw.1, hw.2, hu.1, hu.2]
  have hH := (matchingPhaseWeight_speed_offset_bounds hμ hm hu hv hw).2
  have H1 : |matchingPhaseSlope m v w * (v - w)| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg hf0]
    exact (mul_le_mul hf.2 hd (abs_nonneg _) zero_le_one).trans_eq (by ring)
  have H2 : |(v + w - u) * (matchingPhaseWeight m v w - connectionSpeed m u v w)| ≤ 5 := by
    rw [abs_mul]
    exact (mul_le_mul hS hH (abs_nonneg _) (by norm_num)).trans_eq (by norm_num)
  exact ((abs_add_le _ _).trans (add_le_add H1 H2)).trans_eq (by norm_num)

end BianchiIX
