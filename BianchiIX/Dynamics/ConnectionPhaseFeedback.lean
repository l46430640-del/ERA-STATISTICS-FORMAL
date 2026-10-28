import BianchiIX.Dynamics.ConnectionFeedbackBudget
import BianchiIX.Dynamics.ConnectionForcedVariation
import BianchiIX.Analysis.FeedbackAbsorption

noncomputable section

namespace BianchiIX

open Set MeasureTheory

/-- For a pure phase initial direction, feedback is absorbed without a running maximum or Gronwall. -/
theorem connectionLog_radial_variation_bounds {Y : ℝ → ProjectiveState} {D : ℝ → (Fin 4 → ℝ)}
    {μ a b : ℝ} (hab : a ≤ b) (hμ : 4 ≤ μ)
    (hY : ∀ z ∈ Icc a b, HasDerivAt Y (connectionLogField (Y z)) z)
    (hm : ∀ z ∈ Icc a b, |-Y z 0 - μ| ≤ 1 / 2)
    (hu : ∀ z ∈ Icc a b, 0 ≤ Y z 1 ∧ Y z 1 ≤ 1 / 10000)
    (hv : ∀ z ∈ Icc a b, 0 < Y z 2 ∧ Y z 2 ≤ 1)
    (hw : ∀ z ∈ Icc a b, 0 ≤ Y z 3 ∧ Y z 3 ≤ 1)
    (hentry : Y a 1 ≤ Y a 2) (hsmall : Y a 1 ≤ (1 / 10000) / μ) (hwall : Y a 3 ≤ 1 / 10000)
    (hD : ∀ z ∈ Icc a b, HasDerivAt D (connectionLogLinearizedRates (Y z) (D z)) z)
    (hζ : ∀ z ∈ Icc a b, D z 3 = 0) (hx0 : D a 1 = 0) (hy0 : D a 2 = 0) :
    ∀ t ∈ Icc a b, |D t 0| ≤ (16 / 15) * |D a 0| ∧
      |D t 0 - D a 0| ≤ (16 / 15) * connectionPhaseFeedbackBudget μ (Y a 1) (Y a 2 * Y a 3) * |D a 0| ∧
      ‖connectionWeightedTangent μ (D t)‖ ≤ (2048 / 15) * (t - a) * |D a 0| := by
  let k : ℝ → ℝ := fun z => connectionPhaseFeedbackRate μ (z - a) (Y z 1) (Y z 2 * Y z 3)
  let Λ := connectionPhaseFeedbackBudget μ (Y a 1) (Y a 2 * Y a 3)
  have hμ0 : 0 < μ := by linarith only [hμ]
  have hcY := HasDerivAt.continuousOn hY
  have hcD := HasDerivAt.continuousOn hD
  have hcoords (i : Fin 4) := continuousOn_pi.mp hcY i
  have hk : ContinuousOn k (Icc a b) := by
    dsimp [k, connectionPhaseFeedbackRate]
    fun_prop
  have hk0 (z : ℝ) (hz : z ∈ Icc a b) : 0 ≤ k z :=
    connectionPhaseFeedbackRate_nonneg hμ0.le (sub_nonneg.mpr hz.1) (hu z hz).1
  have hbudget := connectionLog_feedback_budget hab hμ hY hm hu hv hw hentry hsmall hwall
  have hΛ0 : 0 ≤ Λ := connectionPhaseFeedbackBudget_nonneg hμ0.le (hu a ⟨le_rfl, hab⟩).1
  have hΛ : Λ < 1 := hbudget.2.trans_lt (by norm_num)
  have hzero : connectionWeightedTangent μ (D a) = 0 := by simp [connectionWeightedTangent, hx0, hy0]
  have htrans (z : ℝ) (hz : z ∈ Icc a b) :
      ‖connectionWeightedTangent μ (D z)‖ ≤ 128 * ∫ r in a..z, |D r 0| := by
    have H := connectionLog_weighted_variation_bound hab hμ hY hm hu hv hw hentry hsmall hwall hD hζ hz
    simpa only [hzero, norm_zero, mul_zero, zero_add, abs_zero, zero_mul, add_zero] using H
  have hcap (Q : ℝ) (hQ : ∀ z ∈ Icc a b, |D z 0| ≤ Q) (z : ℝ) (hz : z ∈ Icc a b) :
      ‖connectionWeightedTangent μ (D z)‖ ≤ 128 * (z - a) * Q := by
    have hsub : Icc a z ⊆ Icc a b := Icc_subset_Icc_right hz.2
    have HI := intervalIntegral.integral_mono_on (μ := volume) hz.1
      (((continuousOn_pi.mp hcD 0).abs.mono hsub).intervalIntegrable_of_Icc hz.1)
      (intervalIntegrable_const (c := Q)) (fun r hr => hQ r (hsub hr))
    rw [intervalIntegral.integral_const, smul_eq_mul] at HI
    exact (htrans z hz).trans ((mul_le_mul_of_nonneg_left HI (by norm_num : (0 : ℝ) ≤ 128)).trans_eq (by ring))
  have H := abs_bounds_of_derivative_feedback (f := fun z => D z 0) (k := k) (Λ := Λ)
    hab (fun z hz => hasDerivAt_pi.mp (hD z hz) 0)
    hk hk0 hbudget.1 hΛ (fun Q _ hQ z hz => ?_)
  · have hfactor : 1 / (1 - Λ) ≤ 16 / 15 :=
      (div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) < 15 / 16)
        (by linarith only [hbudget.2] : 15 / 16 ≤ 1 - Λ)).trans_eq (by norm_num)
    have hscale (c : ℝ) (hc : 0 ≤ c) : c / (1 - Λ) ≤ (16 / 15) * c := by
      calc
        _ = (1 / (1 - Λ)) * c := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hfactor hc
    have hfinal (z : ℝ) (hz : z ∈ Icc a b) : |D z 0| ≤ (16 / 15) * |D a 0| :=
      (H z hz).1.trans (hscale _ (abs_nonneg _))
    intro t ht
    refine ⟨hfinal t ht, ?_, ?_⟩
    · exact (H t ht).2.trans ((hscale _ (mul_nonneg hΛ0 (abs_nonneg (D a 0)))).trans_eq (by ring))
    · exact (hcap ((16 / 15) * |D a 0|) hfinal t ht).trans_eq (by ring)
  · have Hphase := connectionPhase_variation_bound hμ (hm z hz) (hu z hz)
      ⟨(hv z hz).1.le, (hv z hz).2⟩ (hw z hz) (D z) (hζ z hz)
    have hJ : 0 ≤ 64 * (Y z 1 / μ ^ 2 + (Y z 2 * Y z 3) ^ 2 / μ ^ 4) := by
      have hu0 := (hu z hz).1
      positivity
    have hT : 0 ≤ 64 * (Y z 1 + (Y z 2 * Y z 3) ^ 2 / μ ^ 5) := by
      have hu0 := (hu z hz).1
      positivity
    exact Hphase.trans ((add_le_add (mul_le_mul_of_nonneg_left (hQ z hz) hJ)
      (mul_le_mul_of_nonneg_left (hcap Q hQ z hz) hT)).trans_eq (by dsimp [k, connectionPhaseFeedbackRate]; ring))

end BianchiIX
