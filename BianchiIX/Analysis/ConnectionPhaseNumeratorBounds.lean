import BianchiIX.Analysis.ConnectionPhaseNumerator
import BianchiIX.Analysis.MatchingPhaseWallBounds

noncomputable section

namespace BianchiIX

theorem connectionPhaseNumerator_bounds {μ m u v w : ℝ} (hμ : 4 ≤ μ)
    (hm : |m - μ| ≤ 1 / 2) (hu : 0 ≤ u ∧ u ≤ 1 / 10000)
    (hv : 0 ≤ v ∧ v ≤ 1) (hw : 0 ≤ w ∧ w ≤ 1) :
    |connectionPhaseNumerator m u v w| ≤ 4 * μ ∧
    |connectionPhaseNumeratorPartials m u v w 1| ≤ 3 * μ / 2 * u ∧
    |connectionPhaseNumeratorPartials m u v w 2| ≤ 3 * μ * v ∧
    |connectionPhaseNumeratorPartials m u v w 3| ≤ 3 * μ * w := by
  have hμ0 : 0 < μ := by linarith only [hμ]
  have hμ2 : 16 ≤ μ ^ 2 := by nlinarith only [hμ, sq_nonneg (μ - 4)]
  have hf := matchingPhase_slope_bounds hμ hm hv hw
  have hf0 : 0 ≤ matchingPhaseSlope m v w := by linarith only [hf.1]
  have hH := matchingPhaseWeight_sharp_bounds hμ hm hv hw
  have hwall := matchingPhase_wall_bounds hμ hm hv hw
  have hd : |v - w| ≤ 1 := abs_le.mpr ⟨by linarith only [hv.1, hw.2], by linarith only [hv.2, hw.1]⟩
  have hS : |v + w - u| ≤ 2 := by
    apply abs_le.mpr
    constructor <;> linarith only [hv.1, hv.2, hw.1, hw.2, hu.1, hu.2]
  have fmul (r : ℝ) (hr : 0 ≤ r) : |matchingPhaseSlope m v w * r| ≤ r := by
    rw [abs_mul, abs_of_nonneg hf0, abs_of_nonneg hr]
    exact (mul_le_mul_of_nonneg_right hf.2 hr).trans_eq (by ring)
  have wall_bound (r p q e : ℝ) (hr : 0 ≤ r ∧ r ≤ 1)
      (hp : |p| ≤ 5 * r ^ 2 / μ ^ 2) (hq : |q| ≤ 5 * r ^ 2 / μ ^ 2) (he : |e| ≤ r) :
      |p * (v - w) + e + r * matchingPhaseWeight m v w + (v + w - u) * q| ≤ 3 * μ * r := by
    have H1 : |p * (v - w)| ≤ 5 * r ^ 2 / μ ^ 2 := by
      rw [abs_mul]
      exact (mul_le_mul hp hd (abs_nonneg _) (by positivity)).trans_eq (by ring)
    have H2 : |r * matchingPhaseWeight m v w| ≤ r * (3 * μ / 2) := by
      rw [abs_mul, abs_of_nonneg hr.1, abs_of_pos hH.1]
      exact mul_le_mul_of_nonneg_left hH.2.1 hr.1
    have H3 : |(v + w - u) * q| ≤ 10 * r ^ 2 / μ ^ 2 := by
      rw [abs_mul]
      exact (mul_le_mul hS hq (abs_nonneg _) (by norm_num)).trans_eq (by ring)
    have H := ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)).trans
      (add_le_add (add_le_add ((abs_add_le _ _).trans (add_le_add H1 he)) H2) H3)
    have hr2 : r ^ 2 ≤ r := by nlinarith only [hr.1, hr.2, mul_nonneg hr.1 (sub_nonneg.mpr hr.2)]
    have hsmall : r ^ 2 / μ ^ 2 ≤ r / 16 := div_le_div₀ hr.1 hr2 (by norm_num) hμ2
    have hcoef := mul_le_mul_of_nonneg_right (show (15 / 16 : ℝ) + 1 ≤ 3 * μ / 2 by linarith only [hμ]) hr.1
    calc
      _ ≤ 15 * (r ^ 2 / μ ^ 2) + r + r * (3 * μ / 2) := H.trans_eq (by ring)
      _ ≤ 3 * μ * r := by linarith only [mul_le_mul_of_nonneg_left hsmall (by norm_num : (0 : ℝ) ≤ 15), hcoef]
  refine ⟨?_, ?_, wall_bound v _ _ _ hv hwall.1 hwall.2.2.1 (fmul v hv.1), ?_⟩
  · have H1 : |matchingPhaseSlope m v w * (v - w)| ≤ 1 := by
      rw [abs_mul, abs_of_nonneg hf0]
      exact (mul_le_mul hf.2 hd (abs_nonneg _) zero_le_one).trans_eq (by ring)
    have H2 : |(v + w - u) * matchingPhaseWeight m v w| ≤ 3 * μ := by
      rw [abs_mul, abs_of_pos hH.1]
      exact (mul_le_mul hS hH.2.1 hH.1.le (by norm_num)).trans_eq (by ring)
    exact ((abs_add_le _ _).trans (add_le_add H1 H2)).trans (by linarith only [hμ])
  · change |-u * matchingPhaseWeight m v w| ≤ _
    rw [abs_mul, abs_neg, abs_of_nonneg hu.1, abs_of_pos hH.1]
    exact (mul_le_mul_of_nonneg_left hH.2.1 hu.1).trans_eq (by ring)
  · have He : |-matchingPhaseSlope m v w * w| ≤ w := by simpa only [neg_mul, abs_neg] using fmul w hw.1
    change |matchingPhaseSlopePartials m v w 3 * (v - w) - matchingPhaseSlope m v w * w +
      w * matchingPhaseWeight m v w + (v + w - u) * matchingPhaseWeightPartials m v w 3| ≤ _
    simpa only [sub_eq_add_neg, neg_mul] using wall_bound w _ _ _ hw hwall.2.1 hwall.2.2.2 He

end BianchiIX
