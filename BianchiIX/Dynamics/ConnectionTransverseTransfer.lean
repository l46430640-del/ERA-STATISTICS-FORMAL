import BianchiIX.Dynamics.ConnectionTransverseGrowth
import BianchiIX.Analysis.ForcedRowGrowth

noncomputable section

namespace BianchiIX

open Set

theorem connectionTransverseMatrix_second_row {μ m u v w : ℝ} (hμ : 4 ≤ μ)
    (hm : |m - μ| ≤ 1 / 2) (hu : 0 ≤ u ∧ u ≤ 1 / 10000)
    (hv : 0 ≤ v ∧ v ≤ 1) (hw : 0 ≤ w ∧ w ≤ 1) (huv : u ≤ v) :
    connectionTransverseMatrix μ m u v w 1 1 ≤ 0 ∧
      |connectionTransverseMatrix μ m u v w 1 0| ≤ 64 * μ * u := by
  have hμ0 : 0 < μ := by linarith only [hμ]
  have hm0 : 0 ≤ m := by linarith only [hμ, (abs_le.mp hm).1]
  have hu0 := hu.1
  have hv0 := hv.1
  have hc := connection_coupling_nonneg hu0 hw.1 huv
  have hf : 0 ≤ matchingPhaseSlope m v w := by
    have H := (matchingPhase_slope_bounds hμ hm hv hw).1
    linarith only [H]
  have hK : 0 ≤ phaseNorm (m + 1) v := by dsimp [phaseNorm]; positivity
  have hmy : matchingPhaseVVariation m v w ≤ 0 := by
    unfold matchingPhaseVVariation
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg v)) (mul_nonneg hK hf)
  constructor
  · change (2 * (1 + coupling u v w) * matchingPhaseVVariation m v w - 2 * m * u * v) /
      connectionSpeed m u v w ^ 2 ≤ 0
    apply div_nonpos_of_nonpos_of_nonneg _ (sq_nonneg _)
    exact sub_nonpos.mpr (le_trans (mul_nonpos_of_nonneg_of_nonpos (by positivity) hmy) (by positivity))
  · change |μ ^ 2 * connectionWeakClockPartials m u v w 1| ≤ 64 * μ * u
    rw [abs_mul, abs_of_nonneg (sq_nonneg μ)]
    apply (mul_le_mul_of_nonneg_left (connectionWeakClockPartials_bounds hμ hm hu hv hw).2.1 (sq_nonneg μ)).trans_eq
    field_simp

/-- The nonpositive weak diagonal saves the second scalar propagation factor. -/
theorem connectionLog_transverse_transfer {Y : ℝ → ProjectiveState} {ξ : ℝ → (Fin 2 → ℝ)}
    {μ a b s t : ℝ} (hab : a ≤ b) (hμ : 4 ≤ μ)
    (hY : ∀ z ∈ Icc a b, HasDerivAt Y (connectionLogField (Y z)) z)
    (hm : ∀ z ∈ Icc a b, |-Y z 0 - μ| ≤ 1 / 2)
    (hu : ∀ z ∈ Icc a b, 0 ≤ Y z 1 ∧ Y z 1 ≤ 1 / 10000)
    (hv : ∀ z ∈ Icc a b, 0 < Y z 2 ∧ Y z 2 ≤ 1)
    (hw : ∀ z ∈ Icc a b, 0 ≤ Y z 3 ∧ Y z 3 ≤ 1)
    (hentry : Y a 1 ≤ Y a 2) (hsmall : Y a 1 ≤ (1 / 10000) / μ) (hwall : Y a 3 ≤ 1 / 10000)
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s ≤ t)
    (hξ : ∀ z ∈ Icc s t, HasDerivAt ξ
      ((connectionTransverseMatrix μ (-Y z 0) (Y z 1) (Y z 2) (Y z 3)).mulVec (ξ z)) z)
    (hzero : ξ s 1 = 0) :
    |ξ t 1| ≤ 256 * ‖ξ s‖ * (Y s 1 - Y t 1) := by
  let A := fun z => connectionTransverseMatrix μ (-Y z 0) (Y z 1) (Y z 2) (Y z 3)
  have hsub : Icc s t ⊆ Icc a b := Icc_subset_Icc hs.1 ht.2
  have huv := (connectionLog_prefix_estimates hab hμ hY hm hu hv hw hentry).1
  have hrow (z : ℝ) (hz : z ∈ Icc s t) := connectionTransverseMatrix_second_row hμ (hm z (hsub hz))
    (hu z (hsub hz)) ⟨(hv z (hsub hz)).1.le, (hv z (hsub hz)).2⟩ (hw z (hsub hz)) (huv z (hsub hz))
  have hg (z : ℝ) (hz : z ∈ Icc s t) : ‖ξ z‖ ≤ 2 * ‖ξ s‖ :=
    connectionLog_transverse_growth hab hμ hY hm hu hv hw hentry hsmall hwall hs (hsub hz) hz.1
      (fun r hr => hξ r ⟨hr.1, hr.2.trans hz.2⟩)
  have hξ1 (z : ℝ) (hz : z ∈ Icc s t) :
      HasDerivAt (fun r => ξ r 1) (A z 1 1 * ξ z 1 + A z 1 0 * ξ z 0) z := by
    apply (hasDerivAt_pi.mp (hξ z hz) 1).congr_deriv
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring
  have hB (z : ℝ) (hz : z ∈ Icc s t) :
      HasDerivAt (fun r => 256 * ‖ξ s‖ * (Y s 1 - Y r 1))
        (-256 * ‖ξ s‖ * connectionLogField (Y z) 1) z := by
    convert! ((hasDerivAt_pi.mp (hY z (hsub hz)) 1).const_sub (Y s 1)).const_mul (256 * ‖ξ s‖) using 1
    ring
  apply abs_le_of_forced_nonpos hξ1 (fun z hz => (hrow z hz).1) hB
    (by simp [hzero]) (fun z hz => ?_) t ⟨hst, le_rfl⟩
  have hμ0 : 0 ≤ μ := by linarith only [hμ]
  have hu0 := (hu z (hsub hz)).1
  have hx : |ξ z 0| ≤ 2 * ‖ξ s‖ :=
    (show |ξ z 0| ≤ ‖ξ z‖ by simpa only [Real.norm_eq_abs] using norm_le_pi_norm (ξ z) 0).trans (hg z hz)
  have H : |A z 1 0 * ξ z 0| ≤ 128 * μ * Y z 1 * ‖ξ s‖ := by
    rw [abs_mul]
    calc
      _ ≤ (64 * μ * Y z 1) * (2 * ‖ξ s‖) :=
        mul_le_mul (hrow z hz).2 hx (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have hD : 0 < connectionClockRate (Y z) := by
    have HD := (connection_speed_bounds hμ (hm z (hsub hz)) (hu z (hsub hz))
      ⟨(hv z (hsub hz)).1.le, (hv z (hsub hz)).2⟩ (hw z (hsub hz))).1
    change μ / 2 ≤ connectionClockRate (Y z) at HD
    linarith only [HD, hμ]
  have hU : connectionLogField (Y z) 1 ≤ -μ / 2 * Y z 1 := by
    rw [(connectionLogField_components (ne_of_gt hD)).2.1]
    exact mul_le_mul_of_nonneg_right (connection_strong_clock_rate_le hμ (hm z (hsub hz))
      (hu z (hsub hz)) ⟨(hv z (hsub hz)).1.le, (hv z (hsub hz)).2⟩
      (hw z (hsub hz)) (huv z (hsub hz))) hu0
  have H' := mul_le_mul_of_nonneg_left hU (by positivity : 0 ≤ 256 * ‖ξ s‖)
  dsimp only [A] at H
  linarith only [H, H']

theorem connectionLog_transverse_transfer_decay {Y : ℝ → ProjectiveState} {ξ : ℝ → (Fin 2 → ℝ)}
    {μ a b s t : ℝ} (hab : a ≤ b) (hμ : 4 ≤ μ)
    (hY : ∀ z ∈ Icc a b, HasDerivAt Y (connectionLogField (Y z)) z)
    (hm : ∀ z ∈ Icc a b, |-Y z 0 - μ| ≤ 1 / 2)
    (hu : ∀ z ∈ Icc a b, 0 ≤ Y z 1 ∧ Y z 1 ≤ 1 / 10000)
    (hv : ∀ z ∈ Icc a b, 0 < Y z 2 ∧ Y z 2 ≤ 1)
    (hw : ∀ z ∈ Icc a b, 0 ≤ Y z 3 ∧ Y z 3 ≤ 1)
    (hentry : Y a 1 ≤ Y a 2) (hsmall : Y a 1 ≤ (1 / 10000) / μ) (hwall : Y a 3 ≤ 1 / 10000)
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s ≤ t)
    (hξ : ∀ z ∈ Icc s t, HasDerivAt ξ
      ((connectionTransverseMatrix μ (-Y z 0) (Y z 1) (Y z 2) (Y z 3)).mulVec (ξ z)) z)
    (hzero : ξ s 1 = 0) :
    |ξ t 1| ≤ 256 * Y a 1 * Real.exp (-μ * (s - a) / 2) * ‖ξ s‖ := by
  have H := connectionLog_transverse_transfer hab hμ hY hm hu hv hw hentry hsmall hwall hs ht hst hξ hzero
  have hsub : Icc a s ⊆ Icc a b := Icc_subset_Icc_right hs.2
  have hdecay := (connectionLog_prefix_estimates hs.1 hμ (fun z hz => hY z (hsub hz))
    (fun z hz => hm z (hsub hz)) (fun z hz => hu z (hsub hz)) (fun z hz => hv z (hsub hz))
    (fun z hz => hw z (hsub hz)) hentry).2.1
  have H' := mul_le_mul_of_nonneg_left ((sub_le_self _ (hu t ht).1).trans hdecay)
    (by positivity : 0 ≤ 256 * ‖ξ s‖)
  exact H.trans (H'.trans_eq (by ring))

end BianchiIX
