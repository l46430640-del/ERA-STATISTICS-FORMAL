import BianchiIX.Dynamics.MatchingPhase
import BianchiIX.Dynamics.ConnectionProductIntegral
import BianchiIX.Analysis.CoreIntegrals

noncomputable section

namespace BianchiIX

open Set MeasureTheory

/-- A time-independent matching-phase error follows from two dissipative budgets. -/
theorem connectionLog_matchingPhase_drift {Y : ℝ → ProjectiveState} {μ a b : ℝ}
    (hab : a ≤ b) (hμ : 4 ≤ μ)
    (hY : ∀ z ∈ Icc a b, HasDerivAt Y (connectionLogField (Y z)) z)
    (hm : ∀ z ∈ Icc a b, |-Y z 0 - μ| ≤ 1 / 2)
    (hu : ∀ z ∈ Icc a b, 0 ≤ Y z 1 ∧ Y z 1 ≤ 1 / 10000)
    (hv : ∀ z ∈ Icc a b, 0 < Y z 2 ∧ Y z 2 ≤ 1)
    (hw : ∀ z ∈ Icc a b, 0 ≤ Y z 3 ∧ Y z 3 ≤ 1) (hentry : Y a 1 ≤ Y a 2) :
    |matchingPhase (-Y b 0) (Y b 2) (Y b 3) - matchingPhase (-Y a 0) (Y a 2) (Y a 3)| ≤
      20 * Y a 1 / μ + (Y a 2 * Y a 3) ^ 2 / μ ^ 2 := by
  have hμ0 : 0 < μ := by linarith only [hμ]
  have hD (z : ℝ) (hz : z ∈ Icc a b) : 0 < connectionClockRate (Y z) := by
    have H := (connection_speed_bounds hμ (hm z hz) (hu z hz) ⟨(hv z hz).1.le, (hv z hz).2⟩ (hw z hz)).1
    change μ / 2 ≤ connectionClockRate (Y z) at H
    linarith only [H, hμ]
  have hc (i : Fin 4) : ContinuousOn (fun z => Y z i) (Icc a b) :=
    fun z hz => (hasDerivAt_pi.mp (hY z hz) i).continuousAt.continuousWithinAt
  have hcD := (contDiff_connectionClockRate 1).continuous.comp_continuousOn (HasDerivAt.continuousOn hY)
  let U := fun z => Y z 1 / connectionClockRate (Y z)
  let P := fun z => (Y z 2 * Y z 3) ^ 2 / connectionClockRate (Y z)
  have hU : ContinuousOn U (Icc a b) := (hc 1).div hcD (fun z hz => ne_of_gt (hD z hz))
  have hP : ContinuousOn P (Icc a b) := ((hc 2).mul (hc 3) |>.pow 2).div hcD (fun z hz => ne_of_gt (hD z hz))
  have H := abs_sub_le_integral_bound hab
    (fun z hz => hasDerivAt_matchingPhase_connectionLog (hY z hz)
      (by linarith only [hμ, (abs_le.mp (hm z hz)).1]))
    ((hU.const_mul (5 * μ)).add (hP.const_mul (4 / μ ^ 2))) (fun z hz => ?_)
  · have hiU := hU.intervalIntegrable_of_Icc (μ := volume) hab
    have hiP := hP.intervalIntegrable_of_Icc (μ := volume) hab
    simp only [Pi.add_apply] at H
    rw [intervalIntegral.integral_add (hiU.const_mul (5 * μ)) (hiP.const_mul (4 / μ ^ 2)),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at H
    have hUb := (connectionLog_prefix_integrals hab hμ hY hm hu hv hw hentry).2.2
    have hPb := connectionLog_product_integral hab hμ hY hm hu hv hw hentry
    have hsum := add_le_add (mul_le_mul_of_nonneg_left hUb (show 0 ≤ 5 * μ by positivity))
      (mul_le_mul_of_nonneg_left hPb (show 0 ≤ 4 / μ ^ 2 by positivity))
    apply (H.trans hsum).trans_eq
    field_simp
    ring
  · rw [abs_div, abs_of_pos (hD z hz)]
    have H := matchingPhase_rate_bound hμ (hm z hz) (hu z hz) ⟨(hv z hz).1.le, (hv z hz).2⟩ (hw z hz)
    exact (div_le_div_of_nonneg_right H (hD z hz).le).trans_eq (by dsimp [U, P]; ring)

end BianchiIX
