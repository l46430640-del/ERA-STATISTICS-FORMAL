import BianchiIX.Dynamics.ConnectionTransverseDissipation

noncomputable section

namespace BianchiIX

open Set

theorem connectionLog_transverse_budget_antitone {Y : ℝ → ProjectiveState} {μ a b : ℝ}
    (hμ : 4 ≤ μ) (hY : ∀ z ∈ Icc a b, HasDerivAt Y (connectionLogField (Y z)) z)
    (hm : ∀ z ∈ Icc a b, |-Y z 0 - μ| ≤ 1 / 2)
    (hu : ∀ z ∈ Icc a b, 0 ≤ Y z 1 ∧ Y z 1 ≤ 1 / 10000)
    (hv : ∀ z ∈ Icc a b, 0 ≤ Y z 2 ∧ Y z 2 ≤ 1)
    (hw : ∀ z ∈ Icc a b, 0 ≤ Y z 3 ∧ Y z 3 ≤ 1)
    (huv : ∀ z ∈ Icc a b, Y z 1 ≤ Y z 2) :
    AntitoneOn (fun z => connectionTransverseBudget μ (Y z 1) (Y z 2) (Y z 3)) (Icc a b) := by
  have hd (z : ℝ) (hz : z ∈ Icc a b) := hasDerivAt_connectionTransverseBudget (μ := μ) (hY z hz)
  apply antitoneOn_of_deriv_nonpos (convex_Icc a b)
    (fun z hz => (hd z hz).continuousAt.continuousWithinAt)
    (fun z hz => (hd z (interior_subset hz)).differentiableAt.differentiableWithinAt)
  intro z hz
  rw [(hd z (interior_subset hz)).deriv]
  apply (connectionTransverseBudget_dissipation hμ (hm z (interior_subset hz))
    (hu z (interior_subset hz)) (hv z (interior_subset hz)) (hw z (interior_subset hz))
    (huv z (interior_subset hz))).trans
  have hμ0 : 0 ≤ μ := by linarith only [hμ]
  have hu0 := (hu z (interior_subset hz)).1
  have hv0 := (hv z (interior_subset hz)).1
  have hw0 := (hw z (interior_subset hz)).1
  apply neg_nonpos.mpr
  dsimp [connectionTransverseRate]
  positivity

theorem connectionLog_transverse_growth_exp {Y : ℝ → ProjectiveState} {ξ : ℝ → (Fin 2 → ℝ)}
    {μ a b : ℝ} (hab : a ≤ b) (hμ : 4 ≤ μ)
    (hY : ∀ z ∈ Icc a b, HasDerivAt Y (connectionLogField (Y z)) z)
    (hm : ∀ z ∈ Icc a b, |-Y z 0 - μ| ≤ 1 / 2)
    (hu : ∀ z ∈ Icc a b, 0 ≤ Y z 1 ∧ Y z 1 ≤ 1 / 10000)
    (hv : ∀ z ∈ Icc a b, 0 ≤ Y z 2 ∧ Y z 2 ≤ 1)
    (hw : ∀ z ∈ Icc a b, 0 ≤ Y z 3 ∧ Y z 3 ≤ 1)
    (huv : ∀ z ∈ Icc a b, Y z 1 ≤ Y z 2)
    (hξ : ∀ z ∈ Icc a b, HasDerivAt ξ
      ((connectionTransverseMatrix μ (-Y z 0) (Y z 1) (Y z 2) (Y z 3)).mulVec (ξ z)) z) :
    ‖ξ b‖ ≤ ‖ξ a‖ * Real.exp (connectionTransverseBudget μ (Y a 1) (Y a 2) (Y a 3) -
      connectionTransverseBudget μ (Y b 1) (Y b 2) (Y b 3)) := by
  have hd (z : ℝ) (hz : z ∈ Icc a b) := (hasDerivAt_connectionTransverseBudget (μ := μ) (hY z hz)).neg
  have H := norm_le_exp_of_signedRowSum (HasDerivAt.continuousOn hξ)
    (fun z hz => hξ z (Ico_subset_Icc_self hz))
    (fun z hz => (hd z hz).continuousAt.continuousWithinAt)
    (fun z hz => hd z (Ico_subset_Icc_self hz)) (fun z hz i => ?_) b ⟨hab, le_rfl⟩
  · simpa only [Pi.neg_apply, neg_sub_neg] using H
  · have hz' := Ico_subset_Icc_self hz
    have Hr := connectionTransverseMatrix_signedRows hμ (hm z hz') (hu z hz') (hv z hz') (hw z hz') i
    have HE := connectionTransverseBudget_dissipation hμ (hm z hz') (hu z hz') (hv z hz') (hw z hz') (huv z hz')
    linarith only [Hr, HE]

/-- Every ordered subinterval has growth at most two, independent of its duration. -/
theorem connectionLog_transverse_growth {Y : ℝ → ProjectiveState} {ξ : ℝ → (Fin 2 → ℝ)}
    {μ a b s t : ℝ} (hab : a ≤ b) (hμ : 4 ≤ μ)
    (hY : ∀ z ∈ Icc a b, HasDerivAt Y (connectionLogField (Y z)) z)
    (hm : ∀ z ∈ Icc a b, |-Y z 0 - μ| ≤ 1 / 2)
    (hu : ∀ z ∈ Icc a b, 0 ≤ Y z 1 ∧ Y z 1 ≤ 1 / 10000)
    (hv : ∀ z ∈ Icc a b, 0 < Y z 2 ∧ Y z 2 ≤ 1)
    (hw : ∀ z ∈ Icc a b, 0 ≤ Y z 3 ∧ Y z 3 ≤ 1)
    (hentry : Y a 1 ≤ Y a 2) (hsmall : Y a 1 ≤ (1 / 10000) / μ) (hwall : Y a 3 ≤ 1 / 10000)
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s ≤ t)
    (hξ : ∀ z ∈ Icc s t, HasDerivAt ξ
      ((connectionTransverseMatrix μ (-Y z 0) (Y z 1) (Y z 2) (Y z 3)).mulVec (ξ z)) z) :
    ‖ξ t‖ ≤ 2 * ‖ξ s‖ := by
  have huv := (connectionLog_prefix_estimates hab hμ hY hm hu hv hw hentry).1
  have hv' (z : ℝ) (hz : z ∈ Icc a b) : 0 ≤ Y z 2 ∧ Y z 2 ≤ 1 := ⟨(hv z hz).1.le, (hv z hz).2⟩
  have hsub : Icc s t ⊆ Icc a b := Icc_subset_Icc hs.1 ht.2
  have H := connectionLog_transverse_growth_exp hst hμ (fun z hz => hY z (hsub hz))
    (fun z hz => hm z (hsub hz)) (fun z hz => hu z (hsub hz))
    (fun z hz => hv' z (hsub hz)) (fun z hz => hw z (hsub hz)) (fun z hz => huv z (hsub hz)) hξ
  have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hanti := connectionLog_transverse_budget_antitone hμ hY hm hu hv' hw huv
  have hE : connectionTransverseBudget μ (Y s 1) (Y s 2) (Y s 3) -
      connectionTransverseBudget μ (Y t 1) (Y t 2) (Y t 3) ≤
      connectionTransverseBudget μ (Y a 1) (Y a 2) (Y a 3) :=
    (sub_le_self _ (connectionTransverseBudget_nonneg (by linarith only [hμ]) (hu t ht).1
      (hv t ht).1.le (hw t ht).1)).trans (hanti ha hs hs.1)
  have he := (Real.exp_le_exp.mpr hE).trans_lt
    (exp_connectionTransverseBudget_lt_two hμ ⟨(hu a ha).1, hsmall⟩ (hv' a ha) ⟨(hw a ha).1, hwall⟩)
  exact H.trans ((mul_le_mul_of_nonneg_left he.le (norm_nonneg _)).trans_eq (mul_comm _ _))

end BianchiIX
