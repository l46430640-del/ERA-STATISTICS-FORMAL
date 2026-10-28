import BianchiIX.Analysis.ForcedBudgetGrowth
import BianchiIX.Dynamics.ConnectionTransverseGrowth
import BianchiIX.Analysis.ConnectionWeightedVariation

noncomputable section

namespace BianchiIX

open Set MeasureTheory

theorem connectionLog_transverse_forced_exp {Y : ℝ → ProjectiveState} {ξ q : ℝ → (Fin 2 → ℝ)}
    {R : ℝ → ℝ} {μ a b : ℝ} (hab : a ≤ b) (hμ : 4 ≤ μ)
    (hY : ∀ z ∈ Icc a b, HasDerivAt Y (connectionLogField (Y z)) z)
    (hm : ∀ z ∈ Icc a b, |-Y z 0 - μ| ≤ 1 / 2)
    (hu : ∀ z ∈ Icc a b, 0 ≤ Y z 1 ∧ Y z 1 ≤ 1 / 10000)
    (hv : ∀ z ∈ Icc a b, 0 ≤ Y z 2 ∧ Y z 2 ≤ 1)
    (hw : ∀ z ∈ Icc a b, 0 ≤ Y z 3 ∧ Y z 3 ≤ 1)
    (huv : ∀ z ∈ Icc a b, Y z 1 ≤ Y z 2)
    (hξ : ∀ z ∈ Icc a b, HasDerivAt ξ
      ((connectionTransverseMatrix μ (-Y z 0) (Y z 1) (Y z 2) (Y z 3)).mulVec (ξ z) + q z) z)
    (hR : ContinuousOn R (Icc a b)) (hq : ∀ z ∈ Icc a b, ‖q z‖ ≤ R z) :
    ‖ξ b‖ ≤ Real.exp (connectionTransverseBudget μ (Y a 1) (Y a 2) (Y a 3) -
      connectionTransverseBudget μ (Y b 1) (Y b 2) (Y b 3)) * (‖ξ a‖ + ∫ z in a..b, R z) := by
  have hanti := connectionLog_transverse_budget_antitone hμ hY hm hu hv hw huv
  apply norm_le_integral_envelope_of_forced_budget hab hξ
    (fun z hz => hasDerivAt_connectionTransverseBudget (μ := μ) (hY z hz))
    (fun z hz i => ?_) (fun z hz => hanti ⟨le_rfl, hab⟩ hz hz.1) hR hq
  have Hr := connectionTransverseMatrix_signedRows hμ (hm z hz) (hu z hz) (hv z hz) (hw z hz) i
  have HE := connectionTransverseBudget_dissipation hμ (hm z hz) (hu z hz) (hv z hz) (hw z hz) (huv z hz)
  linarith only [Hr, HE]

/-- The same factor two controls continuous forcing on every ordered subinterval. -/
theorem connectionLog_transverse_forced {Y : ℝ → ProjectiveState} {ξ q : ℝ → (Fin 2 → ℝ)}
    {R : ℝ → ℝ} {μ a b s t : ℝ} (hab : a ≤ b) (hμ : 4 ≤ μ)
    (hY : ∀ z ∈ Icc a b, HasDerivAt Y (connectionLogField (Y z)) z)
    (hm : ∀ z ∈ Icc a b, |-Y z 0 - μ| ≤ 1 / 2)
    (hu : ∀ z ∈ Icc a b, 0 ≤ Y z 1 ∧ Y z 1 ≤ 1 / 10000)
    (hv : ∀ z ∈ Icc a b, 0 < Y z 2 ∧ Y z 2 ≤ 1)
    (hw : ∀ z ∈ Icc a b, 0 ≤ Y z 3 ∧ Y z 3 ≤ 1)
    (hentry : Y a 1 ≤ Y a 2) (hsmall : Y a 1 ≤ (1 / 10000) / μ) (hwall : Y a 3 ≤ 1 / 10000)
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s ≤ t)
    (hξ : ∀ z ∈ Icc s t, HasDerivAt ξ
      ((connectionTransverseMatrix μ (-Y z 0) (Y z 1) (Y z 2) (Y z 3)).mulVec (ξ z) + q z) z)
    (hR : ContinuousOn R (Icc s t)) (hq : ∀ z ∈ Icc s t, ‖q z‖ ≤ R z) :
    ‖ξ t‖ ≤ 2 * (‖ξ s‖ + ∫ z in s..t, R z) := by
  have huv := (connectionLog_prefix_estimates hab hμ hY hm hu hv hw hentry).1
  have hv' (z : ℝ) (hz : z ∈ Icc a b) : 0 ≤ Y z 2 ∧ Y z 2 ≤ 1 := ⟨(hv z hz).1.le, (hv z hz).2⟩
  have hsub : Icc s t ⊆ Icc a b := Icc_subset_Icc hs.1 ht.2
  have H := connectionLog_transverse_forced_exp hst hμ (fun z hz => hY z (hsub hz))
    (fun z hz => hm z (hsub hz)) (fun z hz => hu z (hsub hz))
    (fun z hz => hv' z (hsub hz)) (fun z hz => hw z (hsub hz)) (fun z hz => huv z (hsub hz)) hξ hR hq
  have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hanti := connectionLog_transverse_budget_antitone hμ hY hm hu hv' hw huv
  have hE : connectionTransverseBudget μ (Y s 1) (Y s 2) (Y s 3) -
      connectionTransverseBudget μ (Y t 1) (Y t 2) (Y t 3) ≤
      connectionTransverseBudget μ (Y a 1) (Y a 2) (Y a 3) :=
    (sub_le_self _ (connectionTransverseBudget_nonneg (by linarith only [hμ]) (hu t ht).1
      (hv t ht).1.le (hw t ht).1)).trans (hanti ha hs hs.1)
  have he := (Real.exp_le_exp.mpr hE).trans_lt
    (exp_connectionTransverseBudget_lt_two hμ ⟨(hu a ha).1, hsmall⟩ (hv' a ha) ⟨(hw a ha).1, hwall⟩)
  have hi : 0 ≤ ∫ z in s..t, R z := intervalIntegral.integral_nonneg hst
    (fun z hz => (norm_nonneg _).trans (hq z hz))
  exact H.trans (mul_le_mul_of_nonneg_right he.le (add_nonneg (norm_nonneg _) hi))

theorem connectionLog_transverse_phase_forcing {Y : ℝ → ProjectiveState} {ξ : ℝ → (Fin 2 → ℝ)}
    {Z : ℝ → ℝ} {μ a b s t : ℝ} (hab : a ≤ b) (hμ : 4 ≤ μ)
    (hY : ∀ z ∈ Icc a b, HasDerivAt Y (connectionLogField (Y z)) z)
    (hm : ∀ z ∈ Icc a b, |-Y z 0 - μ| ≤ 1 / 2)
    (hu : ∀ z ∈ Icc a b, 0 ≤ Y z 1 ∧ Y z 1 ≤ 1 / 10000)
    (hv : ∀ z ∈ Icc a b, 0 < Y z 2 ∧ Y z 2 ≤ 1)
    (hw : ∀ z ∈ Icc a b, 0 ≤ Y z 3 ∧ Y z 3 ≤ 1)
    (hentry : Y a 1 ≤ Y a 2) (hsmall : Y a 1 ≤ (1 / 10000) / μ) (hwall : Y a 3 ≤ 1 / 10000)
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s ≤ t)
    (hξ : ∀ z ∈ Icc s t, HasDerivAt ξ
      ((connectionTransverseMatrix μ (-Y z 0) (Y z 1) (Y z 2) (Y z 3)).mulVec (ξ z) +
        Z z • connectionPhaseColumn μ (Y z)) z)
    (hZ : ContinuousOn Z (Icc s t)) (hzero : ξ s = 0) :
    ‖ξ t‖ ≤ 128 * ∫ z in s..t, |Z z| := by
  have hsub : Icc s t ⊆ Icc a b := Icc_subset_Icc hs.1 ht.2
  have H := connectionLog_transverse_forced hab hμ hY hm hu hv hw hentry hsmall hwall hs ht hst hξ
    (hZ.abs.const_mul 64) (fun z hz => connectionPhaseColumn_forcing hμ (hm z (hsub hz))
      (hu z (hsub hz)) ⟨(hv z (hsub hz)).1.le, (hv z (hsub hz)).2⟩ (hw z (hsub hz)) (Z z))
  simpa only [hzero, norm_zero, zero_add, intervalIntegral.integral_const_mul, ← mul_assoc,
    show (2 : ℝ) * 64 = 128 by norm_num] using H

end BianchiIX
