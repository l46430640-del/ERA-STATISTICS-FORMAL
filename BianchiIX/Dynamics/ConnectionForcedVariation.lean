import BianchiIX.Dynamics.ConnectionForcedGrowth
import BianchiIX.Analysis.ConnectionForcingBounds
import BianchiIX.Dynamics.ConnectionLogFlowVariation

noncomputable section

namespace BianchiIX

open Set MeasureTheory

theorem connectionLog_weighted_variation_bound {Y : ℝ → ProjectiveState} {D : ℝ → (Fin 4 → ℝ)}
    {μ a b t ζ : ℝ} (hab : a ≤ b) (hμ : 4 ≤ μ)
    (hY : ∀ z ∈ Icc a b, HasDerivAt Y (connectionLogField (Y z)) z)
    (hm : ∀ z ∈ Icc a b, |-Y z 0 - μ| ≤ 1 / 2)
    (hu : ∀ z ∈ Icc a b, 0 ≤ Y z 1 ∧ Y z 1 ≤ 1 / 10000)
    (hv : ∀ z ∈ Icc a b, 0 < Y z 2 ∧ Y z 2 ≤ 1)
    (hw : ∀ z ∈ Icc a b, 0 ≤ Y z 3 ∧ Y z 3 ≤ 1)
    (hentry : Y a 1 ≤ Y a 2) (hsmall : Y a 1 ≤ (1 / 10000) / μ) (hwall : Y a 3 ≤ 1 / 10000)
    (hD : ∀ z ∈ Icc a b, HasDerivAt D (connectionLogLinearizedRates (Y z) (D z)) z)
    (hζ : ∀ z ∈ Icc a b, D z 3 = ζ) (ht : t ∈ Icc a b) :
    ‖connectionWeightedTangent μ (D t)‖ ≤ 2 * ‖connectionWeightedTangent μ (D a)‖ +
      128 * (∫ z in a..t, |D z 0|) + 2 * |ζ| * ∫ z in a..t, connectionWallForcingEnvelope μ (Y z) := by
  have hμne : μ ≠ 0 := by linarith only [hμ]
  have hsub : Icc a t ⊆ Icc a b := Icc_subset_Icc_right ht.2
  have hdc := (HasDerivAt.continuousOn hD).mono hsub
  have hphase : ContinuousOn (fun z => 64 * |D z 0|) (Icc a t) :=
    (continuousOn_pi.mp hdc 0).abs.const_mul 64
  have henv : ContinuousOn (fun z => |ζ| * connectionWallForcingEnvelope μ (Y z)) (Icc a t) :=
    ((continuous_connectionWallForcingEnvelope μ).comp_continuousOn
      ((HasDerivAt.continuousOn hY).mono hsub)).const_mul |ζ|
  have hder (z : ℝ) (hz : z ∈ Icc a t) := hasDerivAt_connectionWeightedTangent hμne (hD z (hsub hz))
  have H := connectionLog_transverse_forced hab hμ hY hm hu hv hw hentry hsmall hwall
    ⟨le_rfl, hab⟩ ht ht.1
    (fun z hz => by simpa only [hζ z (hsub hz), add_assoc] using hder z hz)
    (hphase.add henv) (fun z hz => connectionWeighted_forcing_bound hμ (hm z (hsub hz))
      (hu z (hsub hz)) ⟨(hv z (hsub hz)).1.le, (hv z (hsub hz)).2⟩ (hw z (hsub hz)) (D z 0) ζ)
  simp only [Pi.add_apply] at H
  rw [intervalIntegral.integral_add (hphase.intervalIntegrable_of_Icc ht.1)
    (henv.intervalIntegrable_of_Icc ht.1), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at H
  convert H using 1
  ring

/-- The estimate is applied to the actual initial derivative of the exact Einstein flow. -/
theorem connectionLog_actual_weighted_variation_bound {y : ProjectiveState} {q : ℝ → ℝ}
    {t₀ μ a b t : ℝ} (hab : a ≤ b) (hμ : 4 ≤ μ) (hden : 0 < projectiveStateDenom y)
    (hdom : ∀ z ∈ Icc a b, q z ∈ normalizedMaxDomain (fromProjectiveState y) t₀)
    (hchart : ∀ z ∈ Icc a b, 0 < 1 + normalizedMaxCurve (fromProjectiveState y) t₀ (q z) 0)
    (hm : ∀ z ∈ Icc a b, |-projectiveOriginalFlow y t₀ (q z) 0 - μ| ≤ 1 / 2)
    (hu : ∀ z ∈ Icc a b, 0 < projectiveOriginalFlow y t₀ (q z) 1 ∧
      projectiveOriginalFlow y t₀ (q z) 1 ≤ 1 / 10000)
    (hv : ∀ z ∈ Icc a b, 0 < projectiveOriginalFlow y t₀ (q z) 2 ∧
      projectiveOriginalFlow y t₀ (q z) 2 ≤ 1)
    (hw : ∀ z ∈ Icc a b, 0 < projectiveOriginalFlow y t₀ (q z) 3 ∧
      projectiveOriginalFlow y t₀ (q z) 3 ≤ 1)
    (hentry : projectiveOriginalFlow y t₀ (q a) 1 ≤ projectiveOriginalFlow y t₀ (q a) 2)
    (hsmall : projectiveOriginalFlow y t₀ (q a) 1 ≤ (1 / 10000) / μ)
    (hwall : projectiveOriginalFlow y t₀ (q a) 3 ≤ 1 / 10000)
    (hq : ∀ z ∈ Icc a b,
      HasDerivAt q (1 / connectionOriginalClockRate (projectiveOriginalFlow y t₀ (q z))) z)
    (v : ProjectiveState) (ht : t ∈ Icc a b) :
    ‖connectionWeightedTangent μ (connectionLogFlowVariation y t₀ (q t) v)‖ ≤
      2 * ‖connectionWeightedTangent μ (connectionLogFlowVariation y t₀ (q a) v)‖ +
      128 * (∫ z in a..t, |connectionLogFlowVariation y t₀ (q z) v 0|) +
      2 * |v 3 / y 3| * ∫ z in a..t, connectionWallForcingEnvelope μ (projectiveOriginalFlow y t₀ (q z)) := by
  have hu' (z : ℝ) (hz : z ∈ Icc a b) : 0 ≤ projectiveOriginalFlow y t₀ (q z) 1 ∧
      projectiveOriginalFlow y t₀ (q z) 1 ≤ 1 / 10000 := ⟨(hu z hz).1.le, (hu z hz).2⟩
  have hv' (z : ℝ) (hz : z ∈ Icc a b) : 0 ≤ projectiveOriginalFlow y t₀ (q z) 2 ∧
      projectiveOriginalFlow y t₀ (q z) 2 ≤ 1 := ⟨(hv z hz).1.le, (hv z hz).2⟩
  have hw' (z : ℝ) (hz : z ∈ Icc a b) : 0 ≤ projectiveOriginalFlow y t₀ (q z) 3 ∧
      projectiveOriginalFlow y t₀ (q z) 3 ≤ 1 := ⟨(hw z hz).1.le, (hw z hz).2⟩
  have hclock (z : ℝ) (hz : z ∈ Icc a b) : connectionClockRate (projectiveOriginalFlow y t₀ (q z)) ≠ 0 := by
    have H := (connection_speed_bounds hμ (hm z hz) (hu' z hz) (hv' z hz) (hw' z hz)).1
    change μ / 2 ≤ connectionClockRate (projectiveOriginalFlow y t₀ (q z)) at H
    linarith only [H, hμ]
  have hfield (z : ℝ) (hz : z ∈ Icc a b) :=
    hasDerivAt_projectiveOriginalFlow_connectionLog (y := y) (t₀ := t₀) (z := z) (q := q)
      hden (hdom z hz) (hchart z hz) (hclock z hz) (hq z hz)
  have hvar (z : ℝ) (hz : z ∈ Icc a b) :=
    hasDerivAt_connectionLogFlowVariation (y := y) (t₀ := t₀) (z := z) (q := q)
      hden (hdom z hz) (hchart z hz)
      (by linarith only [hμ, (abs_le.mp (hm z hz)).1]) (hclock z hz)
      (by have H := (matchingPhase_slope_bounds hμ (hm z hz) (hv' z hz) (hw' z hz)).1; linarith only [H])
      (ne_of_gt (hu z hz).1) (ne_of_gt (hv z hz).1) (ne_of_gt (hw z hz).1) (hq z hz) v
  exact connectionLog_weighted_variation_bound
    (Y := fun z => projectiveOriginalFlow y t₀ (q z)) (D := fun z => connectionLogFlowVariation y t₀ (q z) v)
    hab hμ hfield hm hu' hv hw' hentry hsmall hwall hvar
    (fun z hz => connectionLogFlowVariation_wall v (hclock z hz) (ne_of_gt (hw z hz).1)) ht

end BianchiIX
