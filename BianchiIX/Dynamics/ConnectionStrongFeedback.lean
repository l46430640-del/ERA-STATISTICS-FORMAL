import BianchiIX.Dynamics.ConnectionStrongBudget
import BianchiIX.Dynamics.ConnectionShiftedVariation
import BianchiIX.Analysis.FeedbackAbsorption

noncomputable section

namespace BianchiIX

open Set MeasureTheory

theorem connectionLog_strong_variation_bounds {Y : ℝ → ProjectiveState} {D : ℝ → (Fin 4 → ℝ)}
    {μ a b : ℝ} (hab : a ≤ b) (hμ : 4 ≤ μ)
    (hY : ∀ z ∈ Icc a b, HasDerivAt Y (connectionLogField (Y z)) z)
    (hm : ∀ z ∈ Icc a b, |-Y z 0 - μ| ≤ 1 / 2)
    (hu : ∀ z ∈ Icc a b, 0 ≤ Y z 1 ∧ Y z 1 ≤ 1 / 10000)
    (hv : ∀ z ∈ Icc a b, 0 < Y z 2 ∧ Y z 2 ≤ 1)
    (hw : ∀ z ∈ Icc a b, 0 ≤ Y z 3 ∧ Y z 3 ≤ 1)
    (hentry : Y a 1 ≤ Y a 2) (hsmall : Y a 1 ≤ (1 / 10000) / μ) (hwall : Y a 3 ≤ 1 / 10000)
    (hu0 : 0 < Y a 1)
    (hD : ∀ z ∈ Icc a b, HasDerivAt D (connectionLogLinearizedRates (Y z) (D z)) z)
    (hζ : ∀ z ∈ Icc a b, D z 3 = 0)
    (hJ0 : D a 0 = 0) (hx0 : D a 1 = 1 / Y a 1) (hy0 : D a 2 = 0) :
    ∀ t ∈ Icc a b, |D t 0| ≤ 70 / μ ∧
      ‖connectionWeightedTangent μ (D t) - ![1 / Y a 1, 0]‖ ≤ 256 + 8960 * (t - a) / μ := by
  let k : ℝ → ℝ := fun z => connectionPhaseFeedbackRate μ (z - a) (Y z 1) (Y z 2 * Y z 3)
  let e : ℝ → ℝ := fun z => connectionStrongSource μ (Y a 1) (Y z 1) (Y z 2 * Y z 3) (1 / Y a 1)
  let Λ := connectionPhaseFeedbackBudget μ (Y a 1) (Y a 2 * Y a 3)
  have hμ0 : 0 < μ := by linarith only [hμ]
  have hcY := HasDerivAt.continuousOn hY
  have hcD := HasDerivAt.continuousOn hD
  have hcoords (i : Fin 4) := continuousOn_pi.mp hcY i
  have hk : ContinuousOn k (Icc a b) := by dsimp [k, connectionPhaseFeedbackRate]; fun_prop
  have hk0 (z : ℝ) (hz : z ∈ Icc a b) : 0 ≤ k z :=
    connectionPhaseFeedbackRate_nonneg hμ0.le (sub_nonneg.mpr hz.1) (hu z hz).1
  have he : ContinuousOn e (Icc a b) := by dsimp [e, connectionStrongSource]; fun_prop
  have he0 (z : ℝ) (hz : z ∈ Icc a b) : 0 ≤ e z :=
    connectionStrongSource_nonneg hμ0.le hu0.le (hu z hz).1
  have hbudget := connectionLog_feedback_budget hab hμ hY hm hu hv hw hentry hsmall hwall
  have hΛ : Λ < 1 := hbudget.2.trans_lt (by norm_num)
  have hsource : (∫ z in a..b, e z) ≤ 65 / μ := by
    apply (connectionLog_strong_source_budget hab hμ hY hm hu hv hw hentry (1 / Y a 1)).trans
    apply connectionStrongSourceBudget_ordinary hμ ⟨hu0, hsmall⟩
    have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
    refine ⟨mul_nonneg (hv a ha).1.le (hw a ha).1, ?_⟩
    exact (mul_le_mul_of_nonneg_right (hv a ha).2 (hw a ha).1).trans (by simpa using hwall)
  have hcancel : 256 * Y a 1 * |1 / Y a 1| = 256 := by
    rw [abs_of_pos (one_div_pos.mpr hu0)]
    field_simp
  have htrans (z : ℝ) (hz : z ∈ Icc a b) :
      ‖connectionWeightedTangent μ (D z) - ![1 / Y a 1, 0]‖ ≤ 256 + 128 * ∫ r in a..z, |D r 0| := by
    have H := connectionLog_shifted_variation_bound hab hμ hY hm hu hv hw hentry hsmall hwall hD hζ hx0 hy0 hz
    simpa only [hcancel] using H
  have hcap (Q : ℝ) (hQ : ∀ z ∈ Icc a b, |D z 0| ≤ Q) (z : ℝ) (hz : z ∈ Icc a b) :
      ‖connectionWeightedTangent μ (D z) - ![1 / Y a 1, 0]‖ ≤ 256 + 128 * (z - a) * Q := by
    have hsub : Icc a z ⊆ Icc a b := Icc_subset_Icc_right hz.2
    have HI := intervalIntegral.integral_mono_on (μ := volume) hz.1
      (((continuousOn_pi.mp hcD 0).abs.mono hsub).intervalIntegrable_of_Icc hz.1)
      (intervalIntegrable_const (c := Q)) (fun r hr => hQ r (hsub hr))
    rw [intervalIntegral.integral_const, smul_eq_mul] at HI
    exact (htrans z hz).trans ((add_le_add (le_refl _)
      (mul_le_mul_of_nonneg_left HI (by norm_num : (0 : ℝ) ≤ 128))).trans_eq (by ring))
  have H := abs_bounds_of_forced_derivative_feedback (f := fun z => D z 0) (k := k) (e := e) (Λ := Λ)
    hab (fun z hz => hasDerivAt_pi.mp (hD z hz) 0) hk hk0 he he0 hbudget.1 hΛ (fun Q _ hQ z hz => ?_)
  · have hfinal (z : ℝ) (hz : z ∈ Icc a b) : |D z 0| ≤ 70 / μ := by
      have Hz := (H z hz).1
      rw [hJ0, abs_zero, zero_add] at Hz
      apply Hz.trans
      calc
        _ ≤ (65 / μ) / (1 - Λ) := div_le_div_of_nonneg_right hsource (sub_pos.mpr hΛ).le
        _ ≤ (65 / μ) / (15 / 16) := div_le_div_of_nonneg_left (by positivity)
          (by norm_num : (0 : ℝ) < 15 / 16) (by linarith only [hbudget.2])
        _ ≤ 70 / μ := by
          have Hconst : (65 : ℝ) / (15 / 16) ≤ 70 := by norm_num
          calc
            _ = (65 / (15 / 16)) / μ := by ring
            _ ≤ _ := div_le_div_of_nonneg_right Hconst hμ0.le
    intro t ht
    exact ⟨hfinal t ht, (hcap (70 / μ) hfinal t ht).trans_eq (by ring)⟩
  · have Hphase := connectionPhase_shifted_variation_bound hμ (hm z hz) (hu z hz)
      ⟨(hv z hz).1.le, (hv z hz).2⟩ (hw z hz) (D z) (hζ z hz) (1 / Y a 1)
    have hJ : 0 ≤ 64 * (Y z 1 / μ ^ 2 + (Y z 2 * Y z 3) ^ 2 / μ ^ 4) := by
      have hu' := (hu z hz).1
      positivity
    have hT : 0 ≤ 64 * (Y z 1 + (Y z 2 * Y z 3) ^ 2 / μ ^ 5) := by
      have hu' := (hu z hz).1
      positivity
    have Hbound := Hphase.trans (add_le_add
      (add_le_add (le_refl _) (mul_le_mul_of_nonneg_left (hQ z hz) hJ))
      (mul_le_mul_of_nonneg_left (hcap Q hQ z hz) hT))
    apply Hbound.trans_eq
    dsimp [e, k, connectionStrongSource, connectionPhaseFeedbackRate]
    rw [abs_of_pos (one_div_pos.mpr hu0)]
    field_simp
    ring

theorem connectionShiftedTangent_component_bounds {μ x R : ℝ} {d : Fin 4 → ℝ}
    (hμ : 0 < μ) (hbound : ‖connectionWeightedTangent μ d - ![x, 0]‖ ≤ R) :
    |d 1| ≤ |x| + R ∧ |d 2| ≤ R / μ ^ 2 := by
  have hx : |d 1 - x| ≤ R := by
    simpa [connectionWeightedTangent, Real.norm_eq_abs] using
      (norm_le_pi_norm (connectionWeightedTangent μ d - ![x, 0]) 0).trans hbound
  have hy : μ ^ 2 * |d 2| ≤ R := by
    simpa [connectionWeightedTangent, Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg μ)] using
      (norm_le_pi_norm (connectionWeightedTangent μ d - ![x, 0]) 1).trans hbound
  refine ⟨?_, (le_div_iff₀ (sq_pos_of_pos hμ)).mpr (by simpa only [mul_comm] using hy)⟩
  have H : |d 1| ≤ |d 1 - x| + |x| := by simpa using abs_add_le (d 1 - x) x
  linarith only [H, hx]

end BianchiIX
