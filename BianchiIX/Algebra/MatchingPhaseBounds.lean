import BianchiIX.Algebra.MatchingPhase

noncomputable section

namespace BianchiIX

theorem phaseNorm_ratio_bounds {a b : ℝ} (ha : 2 ≤ a) (hb : 0 ≤ b ∧ b ≤ 1) :
    7 / 8 ≤ a / phaseNorm a b ∧ a / phaseNorm a b ≤ 1 := by
  have ha0 : 0 < a := by linarith only [ha]
  have hn := phaseNorm_pos (b := b) ha0
  have hb2 : b ^ 2 ≤ 1 := by simpa using pow_le_pow_left₀ hb.1 hb.2 2
  have ha2 : 4 ≤ a ^ 2 := by nlinarith only [ha, sq_nonneg (a - 2)]
  have hupper : phaseNorm a b ≤ 8 * a / 7 := by
    nlinarith only [phaseNorm_sq a b, hb2, ha2, hn, ha0]
  exact ⟨(le_div_iff₀ hn).mpr (by linarith only [hupper]),
    (div_le_one hn).mpr (phaseNorm_ge ha0.le)⟩

theorem matchingPhase_slope_bounds {μ m v w : ℝ} (hμ : 4 ≤ μ) (hm : |m - μ| ≤ 1 / 2)
    (hv : 0 ≤ v ∧ v ≤ 1) (hw : 0 ≤ w ∧ w ≤ 1) :
    3 / 4 ≤ matchingPhaseSlope m v w ∧ matchingPhaseSlope m v w ≤ 1 := by
  have hp := phaseNorm_ratio_bounds (by linarith only [hμ, (abs_le.mp hm).1] : 2 ≤ m + 1) hv
  have hn := phaseNorm_ratio_bounds (by linarith only [hμ, (abs_le.mp hm).1] : 2 ≤ m - 1) hw
  dsimp [matchingPhaseSlope]
  constructor <;> linarith only [hp.1, hp.2, hn.1, hn.2]

theorem phaseNormKernel_bounds {μ a b : ℝ} (hμ : 0 < μ) (ha : μ / 2 ≤ a) :
    0 ≤ phaseNormKernel a b ∧ phaseNormKernel a b ≤ 2 / μ ^ 2 := by
  have ha0 : 0 < a := lt_of_lt_of_le (by positivity) ha
  have hn := phaseNorm_pos (b := b) ha0
  have hna := phaseNorm_ge (b := b) ha0.le
  have hprod : μ ^ 2 / 2 ≤ phaseNorm a b * (phaseNorm a b + a) := by
    have H := mul_le_mul (ha.trans hna) (show μ ≤ phaseNorm a b + a by linarith only [ha, hna])
      hμ.le hn.le
    nlinarith only [H]
  have hd : 0 < phaseNorm a b * (phaseNorm a b + a) := mul_pos hn (add_pos hn ha0)
  refine ⟨by unfold phaseNormKernel; positivity, ?_⟩
  have H := one_div_le_one_div_of_le (by positivity : 0 < μ ^ 2 / 2) hprod
  exact H.trans_eq (by ring)

theorem matchingPhase_kernel_bound {μ m v w : ℝ} (hμ : 4 ≤ μ) (hm : |m - μ| ≤ 1 / 2) :
    |matchingPhaseKernel m v w| ≤ 4 / μ ^ 2 := by
  have hμ0 : 0 < μ := by linarith only [hμ]
  have hp := phaseNormKernel_bounds (b := v) hμ0 (by linarith only [hμ, (abs_le.mp hm).1] : μ / 2 ≤ m + 1)
  have hn := phaseNormKernel_bounds (b := w) hμ0 (by linarith only [hμ, (abs_le.mp hm).1] : μ / 2 ≤ m - 1)
  have H := abs_sub (phaseNormKernel (m + 1) v) (phaseNormKernel (m - 1) w)
  rw [abs_of_nonneg hp.1, abs_of_nonneg hn.1] at H
  change |phaseNormKernel (m + 1) v - phaseNormKernel (m - 1) w| ≤ _
  exact (H.trans (add_le_add hp.2 hn.2)).trans_eq (by ring)

theorem matchingPhase_weight_bounds {μ m v w : ℝ} (hμ : 4 ≤ μ) (hm : |m - μ| ≤ 1 / 2)
    (hv : 0 ≤ v ∧ v ≤ 1) (hw : 0 ≤ w ∧ w ≤ 1) :
    0 ≤ matchingPhaseWeight m v w ∧ matchingPhaseWeight m v w ≤ 2 * μ := by
  have hm0 : 0 < m := by linarith only [hμ, (abs_le.mp hm).1]
  have hp := phaseNorm_ge (b := v) (show 0 ≤ m + 1 by linarith only [hm0])
  have hn := phaseNorm_ge (b := w) (show 0 ≤ m - 1 by linarith only [hμ, (abs_le.mp hm).1])
  have hp0 : 0 < phaseNorm (m + 1) v := by linarith only [hp, hm0]
  have hn0 : 0 < phaseNorm (m - 1) w := by linarith only [hn, hμ, (abs_le.mp hm).1]
  have hS := matchingPhase_slope_bounds hμ hm hv hw
  have hS0 : 0 ≤ matchingPhaseSlope m v w := by linarith only [hS.1]
  have hv2 : v ^ 2 ≤ 1 := by simpa using pow_le_pow_left₀ hv.1 hv.2 2
  have hw2 : w ^ 2 ≤ 1 := by simpa using pow_le_pow_left₀ hw.1 hw.2 2
  have hvq : v ^ 2 / phaseNorm (m + 1) v ≤ 1 :=
    (div_le_one hp0).mpr (by linarith only [hv2, hp, hm0])
  have hwq : w ^ 2 / phaseNorm (m - 1) w ≤ 1 :=
    (div_le_one hn0).mpr (by linarith only [hw2, hn, hμ, (abs_le.mp hm).1])
  have hprod := mul_le_mul_of_nonneg_left hS.2 hm0.le
  dsimp [matchingPhaseWeight]
  constructor
  · positivity
  · linarith only [hprod, hvq, hwq, hμ, (abs_le.mp hm).2]

theorem matchingPhase_rate_bound {μ m u v w : ℝ} (hμ : 4 ≤ μ) (hm : |m - μ| ≤ 1 / 2)
    (hu : 0 ≤ u ∧ u ≤ 1 / 10000) (hv : 0 ≤ v ∧ v ≤ 1) (hw : 0 ≤ w ∧ w ≤ 1) :
    |matchingPhaseRate m u v w| ≤ 5 * μ * u + 4 / μ ^ 2 * (v * w) ^ 2 := by
  have hS := matchingPhase_slope_bounds hμ hm hv hw
  have hS0 : 0 ≤ matchingPhaseSlope m v w := by linarith only [hS.1]
  have hH := matchingPhase_weight_bounds hμ hm hv hw
  have hR := matchingPhase_kernel_bound (v := v) (w := w) hμ hm
  have hC := connection_coupling_bounds hu.1 hv hw
  have hCabs : |coupling u v w| ≤ 2 * u := by
    apply abs_le.mpr
    have H := mul_le_mul_of_nonneg_left (show u ≤ 2 by linarith only [hu.2]) hu.1
    constructor <;> nlinarith only [H, hC.1, hC.2]
  have hdiff : |v - w| ≤ 1 := abs_le.mpr ⟨by linarith only [hv.1, hw.2], by linarith only [hv.2, hw.1]⟩
  have hfirst : |u * matchingPhaseSlope m v w * (v - w)| ≤ u := by
    rw [abs_mul, abs_mul, abs_of_nonneg hu.1, abs_of_nonneg hS0]
    have H := mul_le_mul (mul_le_mul_of_nonneg_left hS.2 hu.1) hdiff (abs_nonneg _)
      (mul_nonneg hu.1 zero_le_one)
    simpa only [mul_one] using H
  have hsecond : |coupling u v w * matchingPhaseWeight m v w| ≤ 4 * μ * u := by
    rw [abs_mul, abs_of_nonneg hH.1]
    have H := mul_le_mul hCabs hH.2 hH.1 (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hu.1)
    nlinarith only [H]
  have hthird : |(v * w) ^ 2 * matchingPhaseKernel m v w| ≤ 4 / μ ^ 2 * (v * w) ^ 2 := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
    exact (mul_le_mul_of_nonneg_left hR (sq_nonneg _)).trans_eq (mul_comm _ _)
  have H := (abs_sub ((v * w) ^ 2 * matchingPhaseKernel m v w - u * matchingPhaseSlope m v w * (v - w))
    (coupling u v w * matchingPhaseWeight m v w)).trans
    (add_le_add (abs_sub _ _) le_rfl)
  change |matchingPhaseRate m u v w| ≤ _ at H
  have huμ := mul_le_mul_of_nonneg_right (show 1 ≤ μ by linarith only [hμ]) hu.1
  nlinarith only [H, hfirst, hsecond, hthird, huμ]

end BianchiIX
