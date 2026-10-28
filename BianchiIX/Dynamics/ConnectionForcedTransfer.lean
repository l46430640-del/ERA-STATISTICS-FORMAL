import BianchiIX.Dynamics.ConnectionForcedGrowth
import BianchiIX.Dynamics.ConnectionTransverseTransfer
import BianchiIX.Analysis.DissipativeTransfer

noncomputable section

namespace BianchiIX

open Set MeasureTheory

/-- Strong-direction forcing reaches the weak component with a decaying amplitude factor. -/
theorem connectionLog_transverse_forced_transfer {Y : ℝ → ProjectiveState} {ξ : ℝ → (Fin 2 → ℝ)}
    {g : ℝ → ℝ} {μ a b s t : ℝ} (hab : a ≤ b) (hμ : 4 ≤ μ)
    (hY : ∀ z ∈ Icc a b, HasDerivAt Y (connectionLogField (Y z)) z)
    (hm : ∀ z ∈ Icc a b, |-Y z 0 - μ| ≤ 1 / 2)
    (hu : ∀ z ∈ Icc a b, 0 ≤ Y z 1 ∧ Y z 1 ≤ 1 / 10000)
    (hv : ∀ z ∈ Icc a b, 0 < Y z 2 ∧ Y z 2 ≤ 1)
    (hw : ∀ z ∈ Icc a b, 0 ≤ Y z 3 ∧ Y z 3 ≤ 1)
    (hentry : Y a 1 ≤ Y a 2) (hsmall : Y a 1 ≤ (1 / 10000) / μ) (hwall : Y a 3 ≤ 1 / 10000)
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s ≤ t)
    (hξ : ∀ z ∈ Icc s t, HasDerivAt ξ
      ((connectionTransverseMatrix μ (-Y z 0) (Y z 1) (Y z 2) (Y z 3)).mulVec (ξ z) + ![g z, 0]) z)
    (hg : ContinuousOn g (Icc s t)) (hzero : ξ s = 0) :
    |ξ t 1| ≤ 256 * ((∫ z in s..t, Y z 1 * |g z|) - Y t 1 * ∫ z in s..t, |g z|) ∧
      |ξ t 1| ≤ 256 * ∫ z in s..t, Y z 1 * |g z| := by
  let A := fun z => connectionTransverseMatrix μ (-Y z 0) (Y z 1) (Y z 2) (Y z 3)
  have hμ0 : 0 < μ := by linarith only [hμ]
  have hsub : Icc s t ⊆ Icc a b := Icc_subset_Icc hs.1 ht.2
  have huv := (connectionLog_prefix_estimates hab hμ hY hm hu hv hw hentry).1
  have hv' (z : ℝ) (hz : z ∈ Icc a b) : 0 ≤ Y z 2 ∧ Y z 2 ≤ 1 := ⟨(hv z hz).1.le, (hv z hz).2⟩
  have hrow (z : ℝ) (hz : z ∈ Icc s t) := connectionTransverseMatrix_second_row hμ (hm z (hsub hz))
    (hu z (hsub hz)) (hv' z (hsub hz)) (hw z (hsub hz)) (huv z (hsub hz))
  have hnorm (z : ℝ) : ‖![g z, (0 : ℝ)]‖ ≤ |g z| := by
    apply (pi_norm_le_iff_of_nonempty _).mpr
    intro i
    fin_cases i <;> simp [Real.norm_eq_abs]
  have hG (z : ℝ) (hz : z ∈ Icc s t) : ‖ξ z‖ ≤ 2 * ∫ r in s..z, |g r| := by
    have H := connectionLog_transverse_forced hab hμ hY hm hu hv hw hentry hsmall hwall hs (hsub hz) hz.1
      (fun r hr => hξ r ⟨hr.1, hr.2.trans hz.2⟩)
      (hg.abs.mono (Icc_subset_Icc_right hz.2)) (fun r _ => hnorm r)
    simpa only [hzero, norm_zero, zero_add] using H
  have hξ1 (z : ℝ) (hz : z ∈ Icc s t) :
      HasDerivAt (fun r => ξ r 1) (A z 1 1 * ξ z 1 + A z 1 0 * ξ z 0) z := by
    apply (hasDerivAt_pi.mp (hξ z hz) 1).congr_deriv
    simp only [Pi.add_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      Matrix.cons_val_one, Matrix.cons_val_zero, add_zero]
    ring
  have hU (z : ℝ) (hz : z ∈ Icc s t) : connectionLogField (Y z) 1 ≤ -(μ / 2) * Y z 1 := by
    have hD : 0 < connectionClockRate (Y z) := by
      have HD := (connection_speed_bounds hμ (hm z (hsub hz)) (hu z (hsub hz))
        (hv' z (hsub hz)) (hw z (hsub hz))).1
      change μ / 2 ≤ connectionClockRate (Y z) at HD
      linarith only [HD, hμ]
    rw [(connectionLogField_components (ne_of_gt hD)).2.1]
    simpa only [neg_div, connectionClockRate, connectionSpeed] using mul_le_mul_of_nonneg_right
      (connection_strong_clock_rate_le hμ (hm z (hsub hz)) (hu z (hsub hz))
        (hv' z (hsub hz)) (hw z (hsub hz)) (huv z (hsub hz))) (hu z (hsub hz)).1
  have hforcing (z : ℝ) (hz : z ∈ Icc s t) :
      |A z 1 0 * ξ z 0| ≤ (128 * μ) * Y z 1 * ∫ r in s..z, |g r| := by
    have hx : |ξ z 0| ≤ 2 * ∫ r in s..z, |g r| :=
      (show |ξ z 0| ≤ ‖ξ z‖ by simpa only [Real.norm_eq_abs] using norm_le_pi_norm (ξ z) 0).trans (hG z hz)
    have hu0 := (hu z (hsub hz)).1
    rw [abs_mul]
    apply (mul_le_mul (hrow z hz).2 hx (abs_nonneg _) (by positivity)).trans_eq
    ring
  have H := abs_le_integral_of_dissipative_transfer hst (by positivity : 0 ≤ 128 * μ)
    (by positivity : 0 < μ / 2) hξ1 (fun z hz => (hrow z hz).1)
    (fun z hz => hasDerivAt_pi.mp (hY z (hsub hz)) 1) hU
    (fun z hz => (hu z (hsub hz)).1) hg.abs (fun z _ => abs_nonneg (g z))
    (by simp [hzero]) hforcing
  have hconst : 128 * μ / (μ / 2) = (256 : ℝ) := by field_simp; norm_num
  rwa [hconst] at H

end BianchiIX
