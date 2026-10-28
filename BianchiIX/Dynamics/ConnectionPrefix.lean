import BianchiIX.Dynamics.ConnectionClock
import BianchiIX.Dynamics.CoreContraction
import BianchiIX.Analysis.ScalarMultiplier

noncomputable section

namespace BianchiIX

open Set MeasureTheory

theorem hasDerivAt_connectionLog_ratio {Y : ℝ → ProjectiveState} {z : ℝ}
    (hY : HasDerivAt Y (connectionLogField (Y z)) z)
    (hD : connectionClockRate (Y z) ≠ 0) (hv : Y z 2 ≠ 0) :
    HasDerivAt (fun t => Y t 1 / Y t 2)
      ((connectionStrongRate (-Y z 0) (Y z 1) (Y z 2) (Y z 3) - Y z 0 + 1 +
        coupling (Y z 1) (Y z 2) (Y z 3)) / connectionClockRate (Y z) * (Y z 1 / Y z 2)) z := by
  have H := (hasDerivAt_pi.mp hY 1).div (hasDerivAt_pi.mp hY 2) hv
  rw [(connectionLogField_components hD).2.1, (connectionLogField_components hD).2.2.1] at H
  convert! H using 1
  field_simp
  ring

theorem hasDerivAt_connectionLog_product {Y : ℝ → ProjectiveState} {z : ℝ}
    (hY : HasDerivAt Y (connectionLogField (Y z)) z) (hD : connectionClockRate (Y z) ≠ 0) :
    HasDerivAt (fun t => Y t 2 * Y t 3)
      ((-2 * (1 + coupling (Y z 1) (Y z 2) (Y z 3)) / connectionClockRate (Y z)) * (Y z 2 * Y z 3)) z := by
  have H := (hasDerivAt_pi.mp hY 2).mul (hasDerivAt_pi.mp hY 3)
  rw [(connectionLogField_components hD).2.2.1, (connectionLogField_components hD).2.2.2] at H
  convert! H using 1
  dsimp [connectionClockRate, connectionSpeed] at *
  field_simp
  ring

theorem connectionLog_ratio_antitone {I : Set ℝ} (hI : Convex ℝ I)
    {Y : ℝ → ProjectiveState} {μ : ℝ} (hμ : 4 ≤ μ)
    (hY : ∀ z ∈ I, HasDerivAt Y (connectionLogField (Y z)) z)
    (hm : ∀ z ∈ I, |-Y z 0 - μ| ≤ 1 / 2)
    (hu : ∀ z ∈ I, 0 ≤ Y z 1 ∧ Y z 1 ≤ 1 / 10000)
    (hv : ∀ z ∈ I, 0 < Y z 2 ∧ Y z 2 ≤ 1)
    (hw : ∀ z ∈ I, 0 ≤ Y z 3 ∧ Y z 3 ≤ 1) :
    AntitoneOn (fun z => Y z 1 / Y z 2) I := by
  have hD (z : ℝ) (hz : z ∈ I) : 0 < connectionClockRate (Y z) := by
    have H := (connection_speed_bounds hμ (hm z hz) (hu z hz) ⟨(hv z hz).1.le, (hv z hz).2⟩ (hw z hz)).1
    change μ / 2 ≤ connectionClockRate (Y z) at H
    linarith only [H, hμ]
  have hd (z : ℝ) (hz : z ∈ I) :=
    hasDerivAt_connectionLog_ratio (hY z hz) (ne_of_gt (hD z hz)) (ne_of_gt (hv z hz).1)
  apply antitoneOn_of_deriv_nonpos hI
    (fun z hz => (hd z hz).continuousAt.continuousWithinAt)
    (fun z hz => (hd z (interior_subset hz)).differentiableAt.differentiableWithinAt)
  intro z hz
  rw [(hd z (interior_subset hz)).deriv]
  apply mul_nonpos_of_nonpos_of_nonneg
  · apply div_nonpos_of_nonpos_of_nonneg _ (hD z (interior_subset hz)).le
    have H := connection_ratio_rate_neg hμ (hm z (interior_subset hz)) (hu z (interior_subset hz))
      ⟨(hv z (interior_subset hz)).1.le, (hv z (interior_subset hz)).2⟩ (hw z (interior_subset hz))
    linarith only [H]
  · exact div_nonneg (hu z (interior_subset hz)).1 (hv z (interior_subset hz)).1.le

theorem connectionLog_growing_wall {Y : ℝ → ProjectiveState} {a b : ℝ} (hab : a ≤ b)
    (hY : ∀ z ∈ Icc a b, HasDerivAt Y (connectionLogField (Y z)) z)
    (hD : ∀ z ∈ Icc a b, connectionClockRate (Y z) ≠ 0) :
    Y b 3 = Y a 3 * Real.exp (b - a) := by
  have H := homogeneous_solution_eq_exp_integral_Icc (r := fun _ => (1 : ℝ)) hab continuousOn_const
    (fun z hz => (hasDerivAt_pi.mp (hY z hz) 3).continuousAt.continuousWithinAt)
    (fun z hz => by
      have H := hasDerivAt_pi.mp (hY z (Ioo_subset_Icc_self hz)) 3
      rw [(connectionLogField_components (hD z (Ioo_subset_Icc_self hz))).2.2.2] at H
      simpa only [one_mul] using H)
  simpa using H

/-- Every completed connection prefix has the decay rates in (B.4); wall ordering is derived. -/
theorem connectionLog_prefix_estimates {Y : ℝ → ProjectiveState} {μ a b : ℝ}
    (hab : a ≤ b) (hμ : 4 ≤ μ)
    (hY : ∀ z ∈ Icc a b, HasDerivAt Y (connectionLogField (Y z)) z)
    (hm : ∀ z ∈ Icc a b, |-Y z 0 - μ| ≤ 1 / 2)
    (hu : ∀ z ∈ Icc a b, 0 ≤ Y z 1 ∧ Y z 1 ≤ 1 / 10000)
    (hv : ∀ z ∈ Icc a b, 0 < Y z 2 ∧ Y z 2 ≤ 1)
    (hw : ∀ z ∈ Icc a b, 0 ≤ Y z 3 ∧ Y z 3 ≤ 1) (hentry : Y a 1 ≤ Y a 2) :
    (∀ z ∈ Icc a b, Y z 1 ≤ Y z 2) ∧
      Y b 1 ≤ Y a 1 * Real.exp (-μ * (b - a) / 2) ∧
      Y b 2 ≤ Y a 2 * Real.exp (-(1 + 2 / μ) * (b - a)) ∧
      Y b 2 * Y b 3 ≤ Y a 2 * Y a 3 * Real.exp (-2 * (b - a) / μ) ∧
      Y b 3 = Y a 3 * Real.exp (b - a) := by
  have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hb : b ∈ Icc a b := ⟨hab, le_rfl⟩
  have hanti := connectionLog_ratio_antitone (convex_Icc a b) hμ hY hm hu hv hw
  have huv (z : ℝ) (hz : z ∈ Icc a b) : Y z 1 ≤ Y z 2 := by
    have H := hanti ha hz hz.1
    have H₀ : Y a 1 / Y a 2 ≤ 1 := (div_le_one (hv a ha).1).mpr hentry
    exact (div_le_one (hv z hz).1).mp (H.trans H₀)
  have hD (z : ℝ) (hz : z ∈ Icc a b) : 0 < connectionClockRate (Y z) := by
    have H := (connection_speed_bounds hμ (hm z hz) (hu z hz) ⟨(hv z hz).1.le, (hv z hz).2⟩ (hw z hz)).1
    change μ / 2 ≤ connectionClockRate (Y z) at H
    linarith only [H, hμ]
  refine ⟨huv, ?_, ?_, ?_, connectionLog_growing_wall hab hY (fun z hz => ne_of_gt (hD z hz))⟩
  · have H := le_exp_of_linear_deriv_le (convex_Icc a b) (c := -μ / 2)
      (fun z hz => hasDerivAt_pi.mp (hY z hz) 1) (fun z hz => ?_) ha hb hab
    · convert! H using 1
      congr 2
      ring
    · rw [(connectionLogField_components (ne_of_gt (hD z hz))).2.1]
      exact mul_le_mul_of_nonneg_right (connection_strong_clock_rate_le hμ (hm z hz) (hu z hz)
        ⟨(hv z hz).1.le, (hv z hz).2⟩ (hw z hz) (huv z hz)) (hu z hz).1
  · apply le_exp_of_linear_deriv_le (convex_Icc a b)
      (fun z hz => hasDerivAt_pi.mp (hY z hz) 2) (fun z hz => ?_) ha hb hab
    rw [(connectionLogField_components (ne_of_gt (hD z hz))).2.2.1]
    have H := (connection_weak_clock_rates hμ (hm z hz) (hu z hz)
      ⟨(hv z hz).1.le, (hv z hz).2⟩ (hw z hz) (huv z hz)).1
    convert! mul_le_mul_of_nonneg_right H (hv z hz).1.le using 1
    simp only [connectionClockRate, neg_neg]
  · have H := le_exp_of_linear_deriv_le (convex_Icc a b) (c := -2 / μ)
      (fun z hz => hasDerivAt_connectionLog_product (hY z hz) (ne_of_gt (hD z hz)))
      (fun z hz => mul_le_mul_of_nonneg_right
        (connection_weak_clock_rates hμ (hm z hz) (hu z hz)
          ⟨(hv z hz).1.le, (hv z hz).2⟩ (hw z hz) (huv z hz)).2
        (mul_nonneg (hv z hz).1.le (hw z hz).1)) ha hb hab
    convert! H using 1
    congr 2
    ring

end BianchiIX
