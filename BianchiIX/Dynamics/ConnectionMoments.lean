import BianchiIX.Dynamics.ConnectionPrefix
import BianchiIX.Analysis.DissipativeMoments

noncomputable section

namespace BianchiIX

open Set MeasureTheory

theorem connectionLog_dissipative_moments {Y : ℝ → ProjectiveState} {μ a b : ℝ}
    (hab : a ≤ b) (hμ : 4 ≤ μ)
    (hY : ∀ z ∈ Icc a b, HasDerivAt Y (connectionLogField (Y z)) z)
    (hm : ∀ z ∈ Icc a b, |-Y z 0 - μ| ≤ 1 / 2)
    (hu : ∀ z ∈ Icc a b, 0 ≤ Y z 1 ∧ Y z 1 ≤ 1 / 10000)
    (hv : ∀ z ∈ Icc a b, 0 < Y z 2 ∧ Y z 2 ≤ 1)
    (hw : ∀ z ∈ Icc a b, 0 ≤ Y z 3 ∧ Y z 3 ≤ 1) (hentry : Y a 1 ≤ Y a 2) :
    (∫ z in a..b, Y z 1) ≤ 2 * Y a 1 / μ ∧
      (∫ z in a..b, (z - a) * Y z 1) ≤ 4 * Y a 1 / μ ^ 2 ∧
      (∫ z in a..b, (Y z 2 * Y z 3) ^ 2) ≤ μ * (Y a 2 * Y a 3) ^ 2 / 4 ∧
      (∫ z in a..b, (z - a) * (Y z 2 * Y z 3) ^ 2) ≤ μ ^ 2 * (Y a 2 * Y a 3) ^ 2 / 16 := by
  have hμ0 : 0 < μ := by linarith only [hμ]
  have huv := (connectionLog_prefix_estimates hab hμ hY hm hu hv hw hentry).1
  have hv' (z : ℝ) (hz : z ∈ Icc a b) : 0 ≤ Y z 2 ∧ Y z 2 ≤ 1 := ⟨(hv z hz).1.le, (hv z hz).2⟩
  have hD (z : ℝ) (hz : z ∈ Icc a b) : 0 < connectionClockRate (Y z) := by
    have H := (connection_speed_bounds hμ (hm z hz) (hu z hz) (hv' z hz) (hw z hz)).1
    change μ / 2 ≤ connectionClockRate (Y z) at H
    linarith only [H, hμ]
  have hU (z : ℝ) (hz : z ∈ Icc a b) : connectionLogField (Y z) 1 ≤ -(μ / 2) * Y z 1 := by
    rw [(connectionLogField_components (ne_of_gt (hD z hz))).2.1]
    simpa only [neg_div, connectionClockRate, connectionSpeed] using mul_le_mul_of_nonneg_right
      (connection_strong_clock_rate_le hμ (hm z hz) (hu z hz) (hv' z hz) (hw z hz) (huv z hz)) (hu z hz).1
  have HU := integral_moments_le_of_linear_dissipation hab (by positivity : 0 < μ / 2)
    (fun z hz => hasDerivAt_pi.mp (hY z hz) 1) hU (hu b ⟨hab, le_rfl⟩).1
  have HP := integral_moments_le_of_linear_dissipation hab (by positivity : 0 < 4 / μ)
    (fun z hz => (hasDerivAt_connectionLog_product (hY z hz) (ne_of_gt (hD z hz))).pow 2)
    (fun z hz => ?_) (sq_nonneg (Y b 2 * Y b 3))
  · refine ⟨HU.1.trans_eq (by ring), HU.2.trans_eq (by ring), HP.1.trans_eq ?_, HP.2.trans_eq ?_⟩
    · simp only [Pi.pow_apply]
      field_simp
    · simp only [Pi.pow_apply]
      field_simp
      norm_num
  · have H := mul_le_mul_of_nonneg_right
      (connection_weak_clock_rates hμ (hm z hz) (hu z hz) (hv' z hz) (hw z hz) (huv z hz)).2
      (by positivity : 0 ≤ 2 * (Y z 2 * Y z 3) ^ 2)
    simp only [Pi.pow_apply, connectionClockRate]
    convert! H using 1 <;> ring

end BianchiIX
