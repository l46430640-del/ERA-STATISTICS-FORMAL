import BianchiIX.Analysis.GrowingWallMoments
import BianchiIX.Dynamics.ConnectionMoments

noncomputable section

namespace BianchiIX

open Set MeasureTheory

theorem connectionLog_growing_moments {Y : ℝ → ProjectiveState} {μ a b : ℝ}
    (hab : a ≤ b) (hμ : 4 ≤ μ)
    (hY : ∀ z ∈ Icc a b, HasDerivAt Y (connectionLogField (Y z)) z)
    (hm : ∀ z ∈ Icc a b, |-Y z 0 - μ| ≤ 1 / 2)
    (hu : ∀ z ∈ Icc a b, 0 ≤ Y z 1 ∧ Y z 1 ≤ 1 / 10000)
    (hv : ∀ z ∈ Icc a b, 0 < Y z 2 ∧ Y z 2 ≤ 1)
    (hw : ∀ z ∈ Icc a b, 0 ≤ Y z 3 ∧ Y z 3 ≤ 1) (hentry : Y a 1 ≤ Y a 2) :
    (∫ z in a..b, Y z 3 ^ 2) ≤ Y b 3 ^ 2 / 2 ∧
      (∫ z in a..b, Y z 1 * Y z 3) ≤ 4 * Y a 1 * Y a 3 / μ ∧
      (∫ z in a..b, Y z 1 * Y z 3 ^ 2) ≤ Y a 1 * Y a 3 ∧
      (∫ z in a..b, Y z 2 * Y z 3) ≤ μ * (Y a 2 * Y a 3) / 2 ∧
      (∫ z in a..b, (Y z 2 * Y z 3) ^ 2 * Y z 3 ^ 2) ≤ (Y a 2 * Y a 3) ^ 2 * Y b 3 ^ 2 / 2 := by
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
  have hW (z : ℝ) (hz : z ∈ Icc a b) : HasDerivAt (fun t => Y t 3) (Y z 3) z := by
    have H := hasDerivAt_pi.mp (hY z hz) 3
    rwa [(connectionLogField_components (ne_of_gt (hD z hz))).2.2.2] at H
  have Hsq := (integral_growing_square hab hW).2
  refine ⟨Hsq, integral_dissipative_growing_product hab hμ
    (fun z hz => hasDerivAt_pi.mp (hY z hz) 1) hU (fun z hz => (hu z hz).1) hW (fun z hz => (hw z hz).1),
    integral_dissipative_growing_square hab hμ
      (fun z hz => hasDerivAt_pi.mp (hY z hz) 1) hU (fun z hz => (hu z hz).1) hW
      (fun z hz => (hw z hz).1) (hw b ⟨hab, le_rfl⟩).2, ?_, ?_⟩
  · have HP := integral_moments_le_of_linear_dissipation hab (by positivity : 0 < 2 / μ)
      (fun z hz => hasDerivAt_connectionLog_product (hY z hz) (ne_of_gt (hD z hz)))
      (fun z hz => ?_) (mul_nonneg (hv b ⟨hab, le_rfl⟩).1.le (hw b ⟨hab, le_rfl⟩).1)
    · exact HP.1.trans_eq (by field_simp)
    · simpa only [neg_div, connectionClockRate, connectionSpeed] using mul_le_mul_of_nonneg_right
        (connection_weak_clock_rates hμ (hm z hz) (hu z hz) (hv' z hz) (hw z hz) (huv z hz)).2
        (mul_nonneg (hv z hz).1.le (hw z hz).1)
  · have hP (z : ℝ) (hz : z ∈ Icc a b) : Y z 2 * Y z 3 ≤ Y a 2 * Y a 3 := by
      have hsub : Icc a z ⊆ Icc a b := Icc_subset_Icc_right hz.2
      have H := (connectionLog_prefix_estimates hz.1 hμ (fun r hr => hY r (hsub hr))
        (fun r hr => hm r (hsub hr)) (fun r hr => hu r (hsub hr))
        (fun r hr => hv r (hsub hr)) (fun r hr => hw r (hsub hr)) hentry).2.2.2.1
      have he : Real.exp (-2 * (z - a) / μ) ≤ 1 := Real.exp_le_one_iff.mpr
        (div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (by norm_num) (sub_nonneg.mpr hz.1)) hμ0.le)
      exact H.trans ((mul_le_mul_of_nonneg_left he (mul_nonneg (hv a ⟨le_rfl, hab⟩).1.le
        (hw a ⟨le_rfl, hab⟩).1)).trans_eq (mul_one _))
    have hc := HasDerivAt.continuousOn hY
    have hcP : ContinuousOn (fun z => (Y z 2 * Y z 3) ^ 2) (Icc a b) :=
      ((continuousOn_pi.mp hc 2).mul (continuousOn_pi.mp hc 3)).pow 2
    have hcW : ContinuousOn (fun z => Y z 3 ^ 2) (Icc a b) := (continuousOn_pi.mp hc 3).pow 2
    have HI := intervalIntegral.integral_mono_on (μ := volume) hab
      ((hcP.mul hcW).intervalIntegrable_of_Icc hab) ((hcW.const_mul ((Y a 2 * Y a 3) ^ 2)).intervalIntegrable_of_Icc hab)
      (fun z hz => mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (mul_nonneg (hv z hz).1.le (hw z hz).1) (hP z hz) 2) (sq_nonneg (Y z 3)))
    rw [intervalIntegral.integral_const_mul] at HI
    exact HI.trans ((mul_le_mul_of_nonneg_left Hsq (sq_nonneg (Y a 2 * Y a 3))).trans_eq (by ring))

end BianchiIX
