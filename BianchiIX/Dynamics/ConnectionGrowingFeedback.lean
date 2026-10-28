import BianchiIX.Dynamics.ConnectionGrowingVariation
import BianchiIX.Dynamics.ConnectionGrowingFeedbackBudget

noncomputable section

namespace BianchiIX

open Set MeasureTheory

theorem connectionLog_growing_variation_bounds {Y : ℝ → ProjectiveState} {D : ℝ → (Fin 4 → ℝ)}
    {μ a b : ℝ} (hab : a ≤ b) (hμ : 4 ≤ μ)
    (hY : ∀ z ∈ Icc a b, HasDerivAt Y (connectionLogField (Y z)) z)
    (hm : ∀ z ∈ Icc a b, |-Y z 0 - μ| ≤ 1 / 2)
    (hu : ∀ z ∈ Icc a b, 0 ≤ Y z 1 ∧ Y z 1 ≤ 1 / 10000)
    (hv : ∀ z ∈ Icc a b, 0 < Y z 2 ∧ Y z 2 ≤ 1)
    (hw : ∀ z ∈ Icc a b, 0 ≤ Y z 3 ∧ Y z 3 ≤ 1)
    (hentry : Y a 1 ≤ Y a 2) (hsmall : Y a 1 ≤ (1 / 10000) / μ) (hwall : Y a 3 ≤ 1 / 10000)
    (hw0 : 0 < Y a 3)
    (hD : ∀ z ∈ Icc a b, HasDerivAt D (connectionLogLinearizedRates (Y z) (D z)) z)
    (hζ : ∀ z ∈ Icc a b, D z 3 = 1 / Y a 3) (hx0 : D a 1 = 0) (hy0 : D a 2 = 0)
    (hJ0 : |D a 0| ≤ 2 * Y a 3 / μ) :
    ∀ t ∈ Icc a b, |D t 0| ≤ 8000 * (Y a 1 + Y a 3) / μ ∧
      |D t 1| ≤ 32 + 12800 * Y a 1 + 96 * Y t 3 ^ 2 / (μ * Y a 3) +
        1024000 * (t - a) * (Y a 1 + Y a 3) / μ ∧
      |D t 2| ≤ (12800 * Y a 1 + 64 * Y t 3 ^ 2 / (μ * Y a 3) +
        1024000 * (t - a) * (Y a 1 + Y a 3) / μ) / μ ^ 2 := by
  let q : ℝ → ℝ := fun z => Y z 3 ^ 2 / (μ * Y a 3)
  let k : ℝ → ℝ := fun z => connectionPhaseFeedbackRate μ (z - a) (Y z 1) (Y z 2 * Y z 3)
  let e : ℝ → ℝ := fun z => connectionGrowingFeedbackSource μ (Y a 1) (Y a 3) (Y z)
  let Λ := connectionPhaseFeedbackBudget μ (Y a 1) (Y a 2 * Y a 3)
  have hμ0 : 0 < μ := by linarith only [hμ]
  have hu0 := (hu a ⟨le_rfl, hab⟩).1
  have hcY := HasDerivAt.continuousOn hY
  have hcD := HasDerivAt.continuousOn hD
  have hcoords (i : Fin 4) := continuousOn_pi.mp hcY i
  have hk : ContinuousOn k (Icc a b) := by dsimp [k, connectionPhaseFeedbackRate]; fun_prop
  have hk0 (z : ℝ) (hz : z ∈ Icc a b) : 0 ≤ k z :=
    connectionPhaseFeedbackRate_nonneg hμ0.le (sub_nonneg.mpr hz.1) (hu z hz).1
  have he : ContinuousOn e (Icc a b) :=
    (continuous_connectionGrowingFeedbackSource μ (Y a 1) (Y a 3)).comp_continuousOn hcY
  have he0 (z : ℝ) (hz : z ∈ Icc a b) : 0 ≤ e z :=
    connectionGrowingFeedbackSource_nonneg hμ0.le hu0 hw0.le (hu z hz).1 (hw z hz).1
  have hbudget := connectionLog_feedback_budget hab hμ hY hm hu hv hw hentry hsmall hwall
  have hΛ : Λ < 1 := hbudget.2.trans_lt (by norm_num)
  have hsource : |D a 0| + (∫ z in a..b, e z) ≤ 7500 * (Y a 1 + Y a 3) / μ :=
    (add_le_add hJ0 (connectionLog_growing_feedback_source_budget hab hμ hY hm hu hv hw hentry hw0)).trans
      (connectionGrowingFeedbackBudget_small hμ ⟨hu0, hsmall⟩ ⟨hw0.le, hwall⟩)
  have htrans := connectionLog_growing_transverse_bounds hab hμ hY hm hu hv hw hentry hsmall hwall hw0 hD hζ hx0 hy0
  have hcap (Q : ℝ) (hQ : ∀ z ∈ Icc a b, |D z 0| ≤ Q) (z : ℝ) (hz : z ∈ Icc a b) :
      |D z 1| ≤ 32 * (1 + q z) + (12800 * Y a 1 + 64 * q z + 128 * (z - a) * Q) ∧
      |D z 2| ≤ (12800 * Y a 1 + 64 * q z + 128 * (z - a) * Q) / μ ^ 2 := by
    have hsub : Icc a z ⊆ Icc a b := Icc_subset_Icc_right hz.2
    have HI := intervalIntegral.integral_mono_on (μ := volume) hz.1
      (((continuousOn_pi.mp hcD 0).abs.mono hsub).intervalIntegrable_of_Icc hz.1)
      (intervalIntegrable_const (c := Q)) (fun r hr => hQ r (hsub hr))
    rw [intervalIntegral.integral_const, smul_eq_mul] at HI
    have H := mul_le_mul_of_nonneg_left HI (by norm_num : (0 : ℝ) ≤ 128)
    refine ⟨(htrans z hz).1.trans ((add_le_add (le_refl _) H).trans_eq (by dsimp [q]; ring)), ?_⟩
    exact (htrans z hz).2.trans ((div_le_div_of_nonneg_right (add_le_add (le_refl _) H) (sq_nonneg μ)).trans_eq (by dsimp [q]; ring))
  have H := abs_bounds_of_forced_derivative_feedback (f := fun z => D z 0) (k := k) (e := e) (Λ := Λ)
    hab (fun z hz => hasDerivAt_pi.mp (hD z hz) 0) hk hk0 he he0 hbudget.1 hΛ (fun Q hQ0 hQ z hz => ?_)
  · have hfinal (z : ℝ) (hz : z ∈ Icc a b) : |D z 0| ≤ 8000 * (Y a 1 + Y a 3) / μ := by
      apply (H z hz).1.trans
      calc
        _ ≤ (7500 * (Y a 1 + Y a 3) / μ) / (1 - Λ) := div_le_div_of_nonneg_right hsource (sub_pos.mpr hΛ).le
        _ ≤ (7500 * (Y a 1 + Y a 3) / μ) / (15 / 16) := div_le_div_of_nonneg_left (by positivity)
          (by norm_num : (0 : ℝ) < 15 / 16) (by linarith only [hbudget.2])
        _ = _ := by ring
    intro t ht
    have HC := hcap (8000 * (Y a 1 + Y a 3) / μ) hfinal t ht
    exact ⟨hfinal t ht, HC.1.trans_eq (by dsimp [q]; ring), HC.2.trans_eq (by dsimp [q]; ring)⟩
  · have hq0 : 0 ≤ q z := by dsimp [q]; positivity
    have htime : 0 ≤ z - a := sub_nonneg.mpr hz.1
    have Hphase := connectionPhase_growing_variation_bound hμ hw0 (hm z hz) (hu z hz)
      ⟨(hv z hz).1.le, (hv z hz).2⟩ (hw z hz) (D z) (hζ z hz)
      (by positivity : 0 ≤ 32 * (1 + q z))
      (by positivity : 0 ≤ 12800 * Y a 1 + 64 * q z + 128 * (z - a) * Q)
      (hcap Q hQ z hz).1 (hcap Q hQ z hz).2
    have hJ : 0 ≤ 64 * (Y z 1 / μ ^ 2 + (Y z 2 * Y z 3) ^ 2 / μ ^ 4) := by
      have hU := (hu z hz).1
      positivity
    apply Hphase.trans ((add_le_add (add_le_add (add_le_add
      (mul_le_mul_of_nonneg_left (hQ z hz) hJ) (le_refl _)) (le_refl _)) (le_refl _)).trans_eq ?_)
    dsimp [e, k, q, connectionGrowingFeedbackSource, connectionPhaseFeedbackRate]
    ring

end BianchiIX
