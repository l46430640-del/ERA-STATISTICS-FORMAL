import BianchiIX.Analysis.ConnectionStrongColumnContinuity
import BianchiIX.Dynamics.ConnectionGrowingSourceIntegrals
import BianchiIX.Analysis.CoreIntegrals

noncomputable section

namespace BianchiIX

open Set MeasureTheory

theorem exists_connectionGrowingPrimitive {Y : ℝ → ProjectiveState} {μ a b : ℝ}
    (hab : a ≤ b) (hμ : 4 ≤ μ)
    (hY : ∀ z ∈ Icc a b, HasDerivAt Y (connectionLogField (Y z)) z)
    (hm : ∀ z ∈ Icc a b, |-Y z 0 - μ| ≤ 1 / 2)
    (hu : ∀ z ∈ Icc a b, 0 ≤ Y z 1 ∧ Y z 1 ≤ 1 / 10000)
    (hv : ∀ z ∈ Icc a b, 0 < Y z 2 ∧ Y z 2 ≤ 1)
    (hw : ∀ z ∈ Icc a b, 0 ≤ Y z 3 ∧ Y z 3 ≤ 1)
    (hentry : Y a 1 ≤ Y a 2) (hw0 : 0 < Y a 3) :
    ∃ F : ℝ → ℝ, F a = 0 ∧
      (∀ z ∈ Icc a b, HasDerivAt F (connectionStrongClockPartials (-Y z 0) (Y z 1) (Y z 2) (Y z 3) 3 / Y a 3) z) ∧
      ∀ z ∈ Icc a b, |F z| ≤ 32 * (1 + Y z 3 ^ 2 / (μ * Y a 3)) := by
  let g : ℝ → ℝ := fun z => connectionStrongClockPartials (-Y z 0) (Y z 1) (Y z 2) (Y z 3) 3 / Y a 3
  have hg : ContinuousOn g (Icc a b) := by
    intro z hz
    have hv' : 0 ≤ Y z 2 ∧ Y z 2 ≤ 1 := ⟨(hv z hz).1.le, (hv z hz).2⟩
    have hD : connectionSpeed (-Y z 0) (Y z 1) (Y z 2) (Y z 3) ≠ 0 := by
      have H := (connection_speed_bounds hμ (hm z hz) (hu z hz) hv' (hw z hz)).1
      linarith only [H, hμ]
    have hf : matchingPhaseSlope (-Y z 0) (Y z 2) (Y z 3) ≠ 0 := by
      have H := (matchingPhase_slope_bounds hμ (hm z hz) hv' (hw z hz)).1
      linarith only [H]
    exact ((continuousAt_connectionStrongWallColumn (hY z hz).continuousAt
      (by linarith only [hμ, (abs_le.mp (hm z hz)).1]) hD hf).div_const (Y a 3)).continuousWithinAt
  let G : ℝ → ℝ := fun z => g (projIcc a b hab z)
  let F : ℝ → ℝ := fun t => ∫ z in a..t, G z
  have hG : Continuous G := hg.domRestrict.comp continuous_projIcc
  have hF0 : F a = 0 := by simp [F]
  have hF (z : ℝ) (hz : z ∈ Icc a b) : HasDerivAt F (g z) z := by
    have H := intervalIntegral.integral_hasDerivAt_right (hG.intervalIntegrable a z)
      hG.stronglyMeasurable.stronglyMeasurableAtFilter hG.continuousAt
    simpa only [G, projIcc_of_mem hab hz] using H
  refine ⟨F, hF0, hF, ?_⟩
  intro t ht
  have hsub : Icc a t ⊆ Icc a b := Icc_subset_Icc_right ht.2
  have hR := (continuous_connectionGrowingSources μ (Y a 3)).1.comp_continuousOn (HasDerivAt.continuousOn hY)
  have H := abs_sub_le_integral_bound ht.1 (fun z hz => hF z (hsub hz)) (hR.mono hsub)
    (fun z hz => (connectionGrowingSources_bound hμ hw0 (hm z (hsub hz)) (hu z (hsub hz))
      ⟨(hv z (hsub hz)).1.le, (hv z (hsub hz)).2⟩ (hw z (hsub hz))).1)
  rw [hF0, sub_zero] at H
  exact H.trans (connectionLog_growing_source_integrals ht.1 hμ (fun z hz => hY z (hsub hz))
    (fun z hz => hm z (hsub hz)) (fun z hz => hu z (hsub hz))
    (fun z hz => hv z (hsub hz)) (fun z hz => hw z (hsub hz)) hentry hw0).1

theorem connectionLog_growing_primitive_transfer {Y : ℝ → ProjectiveState} {F : ℝ → ℝ} {μ a b : ℝ}
    (hab : a ≤ b) (hμ : 4 ≤ μ)
    (hY : ∀ z ∈ Icc a b, HasDerivAt Y (connectionLogField (Y z)) z)
    (hm : ∀ z ∈ Icc a b, |-Y z 0 - μ| ≤ 1 / 2)
    (hu : ∀ z ∈ Icc a b, 0 ≤ Y z 1 ∧ Y z 1 ≤ 1 / 10000)
    (hv : ∀ z ∈ Icc a b, 0 < Y z 2 ∧ Y z 2 ≤ 1)
    (hw : ∀ z ∈ Icc a b, 0 ≤ Y z 3 ∧ Y z 3 ≤ 1)
    (hentry : Y a 1 ≤ Y a 2) (hw0 : 0 < Y a 3) (hF : ContinuousOn F (Icc a b))
    (hbound : ∀ z ∈ Icc a b, |F z| ≤ 32 * (1 + Y z 3 ^ 2 / (μ * Y a 3))) :
    (∫ z in a..b, 64 * μ * Y z 1 * |F z|) ≤ 6144 * Y a 1 := by
  have hμ0 : 0 < μ := by linarith only [hμ]
  have hc := HasDerivAt.continuousOn hY
  have hU : ContinuousOn (fun z => Y z 1) (Icc a b) := continuousOn_pi.mp hc 1
  have hUW : ContinuousOn (fun z => Y z 1 * Y z 3 ^ 2) (Icc a b) := hU.mul ((continuousOn_pi.mp hc 3).pow 2)
  have HI := intervalIntegral.integral_mono_on (μ := volume) hab
    (((hU.const_mul (64 * μ)).mul hF.abs).intervalIntegrable_of_Icc hab)
    (((hU.const_mul (2048 * μ)).add (hUW.const_mul (2048 / Y a 3))).intervalIntegrable_of_Icc hab)
    (fun z hz => ?_)
  · simp only [Pi.add_apply, Pi.mul_apply] at HI
    rw [intervalIntegral.integral_add ((hU.const_mul _).intervalIntegrable_of_Icc hab)
      ((hUW.const_mul _).intervalIntegrable_of_Icc hab), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul] at HI
    have HU := (connectionLog_dissipative_moments hab hμ hY hm hu hv hw hentry).1
    have HUW := (connectionLog_growing_moments hab hμ hY hm hu hv hw hentry).2.2.1
    apply HI.trans ((add_le_add (mul_le_mul_of_nonneg_left HU (by positivity : 0 ≤ 2048 * μ))
      (mul_le_mul_of_nonneg_left HUW (by positivity : 0 ≤ 2048 / Y a 3))).trans_eq ?_)
    field_simp
    ring
  · have hu0 := (hu z hz).1
    apply (mul_le_mul_of_nonneg_left (hbound z hz) (by positivity : 0 ≤ 64 * μ * Y z 1)).trans_eq
    dsimp
    field_simp
    ring

end BianchiIX
