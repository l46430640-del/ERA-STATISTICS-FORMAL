import BianchiIX.Analysis.MatchingPhaseWallDifferential

noncomputable section

namespace BianchiIX

theorem phaseNorm_weighted_ratio_bound {a r l : ℝ} (hl : 0 < l) (ha : l ≤ a) :
    |a * r ^ 2 / phaseNorm a r ^ 3| ≤ r ^ 2 / l ^ 2 := by
  have ha0 := hl.trans_le ha
  have hK := phaseNorm_pos (b := r) ha0
  have hKa := phaseNorm_ge (b := r) ha0.le
  rw [abs_of_nonneg (by positivity : 0 ≤ a * r ^ 2 / phaseNorm a r ^ 3)]
  calc
    _ ≤ phaseNorm a r * r ^ 2 / phaseNorm a r ^ 3 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hKa (sq_nonneg r)) (by positivity)
    _ = r ^ 2 / phaseNorm a r ^ 2 := by field_simp
    _ ≤ r ^ 2 / l ^ 2 := div_le_div_of_nonneg_left (sq_nonneg r) (by positivity)
      (pow_le_pow_left₀ hl.le (ha.trans hKa) 2)

theorem matchingPhase_wall_bounds {μ m v w : ℝ} (hμ : 4 ≤ μ) (hm : |m - μ| ≤ 1 / 2)
    (hv : 0 ≤ v ∧ v ≤ 1) (hw : 0 ≤ w ∧ w ≤ 1) :
    |matchingPhaseSlopePartials m v w 2| ≤ 5 * v ^ 2 / μ ^ 2 ∧
    |matchingPhaseSlopePartials m v w 3| ≤ 5 * w ^ 2 / μ ^ 2 ∧
    |matchingPhaseWeightPartials m v w 2| ≤ 5 * v ^ 2 / μ ^ 2 ∧
    |matchingPhaseWeightPartials m v w 3| ≤ 5 * w ^ 2 / μ ^ 2 := by
  have hμ0 : 0 < μ := by linarith only [hμ]
  have hμne := ne_of_gt hμ0
  have hμ2 : 16 ≤ μ ^ 2 := by nlinarith only [hμ, sq_nonneg (μ - 4)]
  have haux := matchingPhase_auxiliary_m_bounds (v := v) (w := w) hμ hm
  have hvar := matchingPhase_inverse_weighted_bounds hμ hm hv hw
  have hv2 : v ^ 2 ≤ 1 := by simpa using pow_le_pow_left₀ hv.1 hv.2 2
  have hw2 : w ^ 2 ≤ 1 := by simpa using pow_le_pow_left₀ hw.1 hw.2 2
  have hfm : |matchingPhaseSlopeDm m v w| ≤ 9 / μ ^ 3 := by
    rw [abs_of_nonneg haux.1]
    apply haux.2.1.trans
    convert! div_le_div_of_nonneg_right (show 9 * (v ^ 2 + w ^ 2) ≤ 18 by linarith only [hv2, hw2])
      (by positivity : 0 ≤ 2 * μ ^ 3) using 1
    ring
  have hcorr : |matchingPhaseWeightDm m v w - matchingPhaseSlope m v w| ≤ 9 / μ ^ 3 := by
    have hp := phaseNorm_pos (b := v) (show 0 < m + 1 by linarith only [hμ, (abs_le.mp hm).1])
    have hn := phaseNorm_pos (b := w) (show 0 < m - 1 by linarith only [hμ, (abs_le.mp hm).1])
    have hq : 0 ≤ v ^ 2 / phaseNorm (m + 1) v ^ 3 := by positivity
    have hr : 0 ≤ w ^ 2 / phaseNorm (m - 1) w ^ 3 := by positivity
    have H := abs_sub (w ^ 2 / phaseNorm (m - 1) w ^ 3) (v ^ 2 / phaseNorm (m + 1) v ^ 3)
    rw [abs_of_nonneg hq, abs_of_nonneg hr] at H
    calc
      _ = |w ^ 2 / phaseNorm (m - 1) w ^ 3 - v ^ 2 / phaseNorm (m + 1) v ^ 3| := by
        dsimp [matchingPhaseWeightDm]
        congr 1
        ring
      _ ≤ matchingPhaseSlopeDm m v w := H.trans_eq (by dsimp [matchingPhaseSlopeDm]; ring)
      _ ≤ 9 / μ ^ 3 := by simpa only [abs_of_nonneg haux.1] using hfm
  have explicit_bound (a r : ℝ) (ha : 5 * μ / 8 ≤ a) :
      |a * r ^ 2 / phaseNorm a r ^ 3| ≤ 3 * r ^ 2 / μ ^ 2 := by
    apply (phaseNorm_weighted_ratio_bound (r := r) (by positivity : 0 < 5 * μ / 8) ha).trans
    convert! div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (show (64 / 25 : ℝ) ≤ 3 by norm_num) (sq_nonneg r)) (sq_nonneg μ) using 1
    ring
  have hep := explicit_bound (m + 1) v (by linarith only [hμ, (abs_le.mp hm).1])
  have hen := explicit_bound (m - 1) w (by linarith only [hμ, (abs_le.mp hm).1])
  have hnep : |-(m + 1) * v ^ 2 / phaseNorm (m + 1) v ^ 3| ≤ 3 * v ^ 2 / μ ^ 2 := by
    simpa only [neg_mul, neg_div, abs_neg] using hep
  have hnen : |-(m - 1) * w ^ 2 / phaseNorm (m - 1) w ^ 3| ≤ 3 * w ^ 2 / μ ^ 2 := by
    simpa only [neg_mul, neg_div, abs_neg] using hen
  have mixed (r e δ q : ℝ) (he : |e| ≤ 3 * r ^ 2 / μ ^ 2)
      (hδ : |δ| ≤ 3 * r ^ 2 / μ) (hq : |q| ≤ 9 / μ ^ 3) : |e + δ * q| ≤ 5 * r ^ 2 / μ ^ 2 := by
    have Hprod : |δ * q| ≤ 27 * r ^ 2 / μ ^ 4 := by
      rw [abs_mul]
      exact (mul_le_mul hδ hq (abs_nonneg _) (by positivity)).trans_eq (by ring)
    have Hprod' : |δ * q| ≤ 2 * r ^ 2 / μ ^ 2 := Hprod.trans (by
      calc
        _ ≤ 2 * μ ^ 2 * r ^ 2 / μ ^ 4 := div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (by linarith only [hμ2]) (sq_nonneg r)) (by positivity)
        _ = _ := by field_simp)
    exact ((abs_add_le _ _).trans (add_le_add he Hprod')).trans_eq (by ring)
  exact ⟨mixed v _ _ _ hnep hvar.2.1 hfm, mixed w _ _ _ hnen hvar.2.2 hfm,
    mixed v _ _ _ hep hvar.2.1 hcorr, mixed w _ _ _ hnen hvar.2.2 hcorr⟩

end BianchiIX
