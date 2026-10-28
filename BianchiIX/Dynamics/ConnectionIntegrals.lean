import BianchiIX.Dynamics.ConnectionPrefix
import BianchiIX.Analysis.DissipationBudget

noncomputable section

namespace BianchiIX

open Set MeasureTheory

/-- The three finite budgets use projective time, expressed as d ell / D. -/
theorem connectionLog_prefix_integrals {Y : ℝ → ProjectiveState} {μ a b : ℝ}
    (hab : a ≤ b) (hμ : 4 ≤ μ)
    (hY : ∀ z ∈ Icc a b, HasDerivAt Y (connectionLogField (Y z)) z)
    (hm : ∀ z ∈ Icc a b, |-Y z 0 - μ| ≤ 1 / 2)
    (hu : ∀ z ∈ Icc a b, 0 ≤ Y z 1 ∧ Y z 1 ≤ 1 / 10000)
    (hv : ∀ z ∈ Icc a b, 0 < Y z 2 ∧ Y z 2 ≤ 1)
    (hw : ∀ z ∈ Icc a b, 0 ≤ Y z 3 ∧ Y z 3 ≤ 1) (hentry : Y a 1 ≤ Y a 2) :
    (∫ z in a..b, (Y z 2) ^ 2 / connectionClockRate (Y z)) ≤ 1 / (2 * μ) ∧
      (∫ z in a..b, (Y z 3) ^ 2 / connectionClockRate (Y z)) ≤ 1 / μ ∧
      (∫ z in a..b, Y z 1 / connectionClockRate (Y z)) ≤ 4 * Y a 1 / μ ^ 2 := by
  have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hb : b ∈ Icc a b := ⟨hab, le_rfl⟩
  have hμ0 : 0 < μ := by linarith only [hμ]
  have huv := (connectionLog_prefix_estimates hab hμ hY hm hu hv hw hentry).1
  have hD (z : ℝ) (hz : z ∈ Icc a b) : 0 < connectionClockRate (Y z) := by
    have H := (connection_speed_bounds hμ (hm z hz) (hu z hz) ⟨(hv z hz).1.le, (hv z hz).2⟩ (hw z hz)).1
    change μ / 2 ≤ connectionClockRate (Y z) at H
    linarith only [H, hμ]
  have hcoord (i : Fin 4) : ContinuousOn (fun z => Y z i) (Icc a b) :=
    fun z hz => (hasDerivAt_pi.mp (hY z hz) i).continuousAt.continuousWithinAt
  have hcD : ContinuousOn (fun z => connectionClockRate (Y z)) (Icc a b) :=
    (contDiff_connectionClockRate 1).continuous.comp_continuousOn (HasDerivAt.continuousOn hY)
  have hcont (i : Fin 4) : ContinuousOn (fun z => (Y z i) ^ 2 / connectionClockRate (Y z)) (Icc a b) :=
    (hcoord i |>.pow 2).div hcD (fun z hz => ne_of_gt (hD z hz))
  refine ⟨?_, ?_, ?_⟩
  · have H := integral_le_of_dissipation hab (show 0 < 2 * μ by positivity)
      (fun z hz => (hasDerivAt_pi.mp (hY z hz) 2).pow 2) (hcont 2) (fun z hz => ?_) (sq_nonneg (Y b 2))
    · apply H.trans
      apply div_le_div_of_nonneg_right _ (by positivity : 0 ≤ 2 * μ)
      change (Y a 2) ^ 2 ≤ 1
      nlinarith only [(hv a ha).1, (hv a ha).2, mul_nonneg (hv a ha).1.le (sub_nonneg.mpr (hv a ha).2)]
    · rw [(connectionLogField_components (ne_of_gt (hD z hz))).2.2.1]
      have hc := connection_coupling_nonneg (hu z hz).1 (hw z hz).1 (huv z hz)
      have hm' : Y z 0 - 1 - coupling (Y z 1) (Y z 2) (Y z 3) ≤ -μ := by
        linarith only [(abs_le.mp (hm z hz)).1, hc]
      have H := mul_le_mul_of_nonneg_right hm' (sq_nonneg (Y z 2))
      rw [← mul_div_assoc]
      apply (le_div_iff₀ (hD z hz)).mpr
      norm_num only [Nat.reduceSub, pow_one, Nat.cast_ofNat]
      field_simp [ne_of_gt (hD z hz)]
      nlinarith only [H]
  · have H := integral_le_of_dissipation hab hμ0
      (fun z hz => ((hasDerivAt_pi.mp (hY z hz) 3).pow 2).const_sub 1)
      (hcont 3) (fun z hz => ?_)
      (show 0 ≤ 1 - (Y b 3) ^ 2 by
        nlinarith only [(hw b hb).1, (hw b hb).2,
          mul_nonneg (hw b hb).1 (sub_nonneg.mpr (hw b hb).2)])
    · apply H.trans
      apply div_le_div_of_nonneg_right _ hμ0.le
      change 1 - (Y a 3) ^ 2 ≤ 1
      linarith only [sq_nonneg (Y a 3)]
    · rw [(connectionLogField_components (ne_of_gt (hD z hz))).2.2.2]
      have H := (connection_speed_bounds hμ (hm z hz) (hu z hz) ⟨(hv z hz).1.le, (hv z hz).2⟩ (hw z hz)).1
      change μ / 2 ≤ connectionClockRate (Y z) at H
      have H' := mul_le_mul_of_nonneg_right H (sq_nonneg (Y z 3))
      rw [← mul_div_assoc]
      apply (le_div_iff₀ (hD z hz)).mpr
      norm_num only [Nat.reduceSub, pow_one, Nat.cast_ofNat]
      nlinarith only [H']
  · have H := integral_le_of_dissipation hab (show 0 < μ ^ 2 / 4 by positivity)
      (fun z hz => hasDerivAt_pi.mp (hY z hz) 1)
      ((hcoord 1).div hcD (fun z hz => ne_of_gt (hD z hz))) (fun z hz => ?_) (hu b hb).1
    · convert! H using 1
      ring
    · rw [(connectionLogField_components (ne_of_gt (hD z hz))).2.1]
      have H := mul_le_mul_of_nonneg_right
        (connection_strong_rate_le (v := Y z 2) (w := Y z 3) hμ (hm z hz) (hu z hz)) (hu z hz).1
      simp only [Pi.div_apply]
      convert! div_le_div_of_nonneg_right H (hD z hz).le using 1 <;> ring

theorem connectionLog_clock_integral_bounds {Y : ℝ → ProjectiveState} {μ a b : ℝ}
    (hab : a ≤ b) (hμ : 0 < μ) (hY : ContinuousOn Y (Icc a b))
    (hD : ∀ z ∈ Icc a b, μ / 2 ≤ connectionClockRate (Y z) ∧ connectionClockRate (Y z) ≤ μ) :
    (b - a) / μ ≤ (∫ z in a..b, 1 / connectionClockRate (Y z)) ∧
      (∫ z in a..b, 1 / connectionClockRate (Y z)) ≤ 2 * (b - a) / μ := by
  have hDpos (z : ℝ) (hz : z ∈ Icc a b) : 0 < connectionClockRate (Y z) :=
    lt_of_lt_of_le (by positivity) (hD z hz).1
  have hc : ContinuousOn (fun z => 1 / connectionClockRate (Y z)) (Icc a b) :=
    continuousOn_const.div ((contDiff_connectionClockRate 1).continuous.comp_continuousOn hY)
      (fun z hz => ne_of_gt (hDpos z hz))
  have hi := hc.intervalIntegrable_of_Icc (μ := volume) hab
  constructor
  · have H := intervalIntegral.integral_mono_on hab (intervalIntegrable_const (c := 1 / μ)) hi
      (fun z hz => one_div_le_one_div_of_le (hDpos z hz) (hD z hz).2)
    simpa only [intervalIntegral.integral_const, smul_eq_mul, div_eq_mul_inv, one_mul] using H
  · have H := intervalIntegral.integral_mono_on hab hi (intervalIntegrable_const (c := 2 / μ))
      (fun z hz => (one_div_le_one_div_of_le (by positivity : 0 < μ / 2) (hD z hz).1).trans_eq (by ring))
    convert! H using 1
    simp only [intervalIntegral.integral_const, smul_eq_mul]
    ring

end BianchiIX
