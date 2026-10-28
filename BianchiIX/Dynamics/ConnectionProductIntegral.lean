import BianchiIX.Dynamics.ConnectionIntegrals

noncomputable section

namespace BianchiIX

open Set MeasureTheory

/-- The wall product supplies a finite budget without a logarithmic waiting-time loss. -/
theorem connectionLog_product_integral {Y : ℝ → ProjectiveState} {μ a b : ℝ}
    (hab : a ≤ b) (hμ : 4 ≤ μ)
    (hY : ∀ z ∈ Icc a b, HasDerivAt Y (connectionLogField (Y z)) z)
    (hm : ∀ z ∈ Icc a b, |-Y z 0 - μ| ≤ 1 / 2)
    (hu : ∀ z ∈ Icc a b, 0 ≤ Y z 1 ∧ Y z 1 ≤ 1 / 10000)
    (hv : ∀ z ∈ Icc a b, 0 < Y z 2 ∧ Y z 2 ≤ 1)
    (hw : ∀ z ∈ Icc a b, 0 ≤ Y z 3 ∧ Y z 3 ≤ 1) (hentry : Y a 1 ≤ Y a 2) :
    (∫ z in a..b, (Y z 2 * Y z 3) ^ 2 / connectionClockRate (Y z)) ≤ (Y a 2 * Y a 3) ^ 2 / 4 := by
  have huv := (connectionLog_prefix_estimates hab hμ hY hm hu hv hw hentry).1
  have hD (z : ℝ) (hz : z ∈ Icc a b) : 0 < connectionClockRate (Y z) := by
    have H := (connection_speed_bounds hμ (hm z hz) (hu z hz) ⟨(hv z hz).1.le, (hv z hz).2⟩ (hw z hz)).1
    change μ / 2 ≤ connectionClockRate (Y z) at H
    linarith only [H, hμ]
  have hc (i : Fin 4) : ContinuousOn (fun z => Y z i) (Icc a b) :=
    fun z hz => (hasDerivAt_pi.mp (hY z hz) i).continuousAt.continuousWithinAt
  have hcD := (contDiff_connectionClockRate 1).continuous.comp_continuousOn (HasDerivAt.continuousOn hY)
  apply integral_le_of_dissipation hab (by norm_num : (0 : ℝ) < 4)
    (fun z hz => (hasDerivAt_connectionLog_product (hY z hz) (ne_of_gt (hD z hz))).pow 2)
    (((hc 2).mul (hc 3) |>.pow 2).div hcD (fun z hz => ne_of_gt (hD z hz))) ?_ (sq_nonneg _)
  intro z hz
  have hC := connection_coupling_nonneg (hu z hz).1 (hw z hz).1 (huv z hz)
  have H := mul_nonneg hC (sq_nonneg (Y z 2 * Y z 3))
  have H' : -4 * (1 + coupling (Y z 1) (Y z 2) (Y z 3)) * (Y z 2 * Y z 3) ^ 2 ≤
      -4 * (Y z 2 * Y z 3) ^ 2 := by nlinarith only [H]
  simp only [Pi.div_apply, Pi.pow_apply, Pi.mul_apply, Function.comp_apply]
  convert! div_le_div_of_nonneg_right H' (hD z hz).le using 1 <;> ring

end BianchiIX
