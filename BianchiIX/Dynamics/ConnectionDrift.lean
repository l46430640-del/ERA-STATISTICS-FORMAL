import BianchiIX.Dynamics.ConnectionIntegrals
import BianchiIX.Analysis.CoreIntegrals

noncomputable section

namespace BianchiIX

open Set MeasureTheory

/-- The closed phase band improves strictly before any possible failure or next-wall hit. -/
theorem connectionLog_phase_band_improves {Y : ℝ → ProjectiveState} {μ a b : ℝ}
    (hab : a ≤ b) (hμ : 4 ≤ μ)
    (hY : ∀ z ∈ Icc a b, HasDerivAt Y (connectionLogField (Y z)) z)
    (hinit : -Y a 0 = μ)
    (hm : ∀ z ∈ Icc a b, |-Y z 0 - μ| ≤ 1 / 2)
    (hu : ∀ z ∈ Icc a b, 0 ≤ Y z 1 ∧ Y z 1 ≤ 1 / 10000)
    (hv : ∀ z ∈ Icc a b, 0 < Y z 2 ∧ Y z 2 ≤ 1)
    (hw : ∀ z ∈ Icc a b, 0 ≤ Y z 3 ∧ Y z 3 ≤ 1) (hentry : Y a 1 ≤ Y a 2) :
    |-Y b 0 - μ| ≤ (3 / 2 + 12 * Y a 1) / μ ∧ |-Y b 0 - μ| < 1 / 2 := by
  have hμ0 : 0 < μ := by linarith only [hμ]
  have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have huv := (connectionLog_prefix_estimates hab hμ hY hm hu hv hw hentry).1
  have hD (z : ℝ) (hz : z ∈ Icc a b) : 0 < connectionClockRate (Y z) := by
    have H := (connection_speed_bounds hμ (hm z hz) (hu z hz) ⟨(hv z hz).1.le, (hv z hz).2⟩ (hw z hz)).1
    change μ / 2 ≤ connectionClockRate (Y z) at H
    linarith only [H, hμ]
  have hcoord (i : Fin 4) : ContinuousOn (fun z => Y z i) (Icc a b) :=
    fun z hz => (hasDerivAt_pi.mp (hY z hz) i).continuousAt.continuousWithinAt
  have hcD : ContinuousOn (fun z => connectionClockRate (Y z)) (Icc a b) :=
    (contDiff_connectionClockRate 1).continuous.comp_continuousOn (HasDerivAt.continuousOn hY)
  let V : ℝ → ℝ := fun z => (Y z 2) ^ 2 / connectionClockRate (Y z)
  let W : ℝ → ℝ := fun z => (Y z 3) ^ 2 / connectionClockRate (Y z)
  let U : ℝ → ℝ := fun z => Y z 1 / connectionClockRate (Y z)
  have hVc : ContinuousOn V (Icc a b) := (hcoord 2 |>.pow 2).div hcD (fun z hz => ne_of_gt (hD z hz))
  have hWc : ContinuousOn W (Icc a b) := (hcoord 3 |>.pow 2).div hcD (fun z hz => ne_of_gt (hD z hz))
  have hUc : ContinuousOn U (Icc a b) := (hcoord 1).div hcD (fun z hz => ne_of_gt (hD z hz))
  have H := abs_sub_le_integral_bound hab (fun z hz => hasDerivAt_pi.mp (hY z hz) 0)
    ((hVc.add hWc).add (hUc.const_mul (3 * μ))) (fun z hz => ?_)
  · have hiV := hVc.intervalIntegrable_of_Icc (μ := volume) hab
    have hiW := hWc.intervalIntegrable_of_Icc (μ := volume) hab
    have hiU := hUc.intervalIntegrable_of_Icc (μ := volume) hab
    simp only [Pi.add_apply] at H
    rw [intervalIntegral.integral_add (hiV.add hiW) (hiU.const_mul (3 * μ)),
      intervalIntegral.integral_add hiV hiW, intervalIntegral.integral_const_mul] at H
    obtain ⟨hV, hW, hU⟩ := connectionLog_prefix_integrals hab hμ hY hm hu hv hw hentry
    have hsum := add_le_add (add_le_add hV hW)
      (mul_le_mul_of_nonneg_left hU (show 0 ≤ 3 * μ by positivity))
    have hbound : |-Y b 0 - μ| ≤ (3 / 2 + 12 * Y a 1) / μ := by
      have heq : -Y b 0 - μ = -(Y b 0 - Y a 0) := by linarith only [hinit]
      rw [heq, abs_neg]
      apply (H.trans hsum).trans_eq
      field_simp
      ring
    refine ⟨hbound, hbound.trans_lt ?_⟩
    apply (div_lt_iff₀ hμ0).mpr
    linarith only [(hu a ha).2, hμ]
  · rw [(connectionLogField_components (ne_of_gt (hD z hz))).1, abs_div, abs_of_pos (hD z hz)]
    have H := connection_phase_velocity_bound hμ (hm z hz) (hu z hz)
      ⟨(hv z hz).1.le, (hv z hz).2⟩ (hw z hz) (huv z hz)
    simp only [neg_neg] at H
    exact (div_le_div_of_nonneg_right H (hD z hz).le).trans_eq (by dsimp [V, W, U]; ring)

end BianchiIX
