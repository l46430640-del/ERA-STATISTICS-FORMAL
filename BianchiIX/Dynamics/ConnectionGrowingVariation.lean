import BianchiIX.Dynamics.ConnectionGrowingPrimitive
import BianchiIX.Dynamics.ConnectionStrongFeedback

noncomputable section

namespace BianchiIX

open Set MeasureTheory

theorem hasDerivAt_connectionGrowingResidual {D : ℝ → (Fin 4 → ℝ)} {F : ℝ → ℝ}
    {y : ProjectiveState} {μ w t : ℝ} (hμ : μ ≠ 0)
    (hD : HasDerivAt D (connectionLogLinearizedRates y (D t)) t)
    (hF : HasDerivAt F (connectionStrongClockPartials (-y 0) (y 1) (y 2) (y 3) 3 / w) t)
    (hζ : D t 3 = 1 / w) :
    HasDerivAt (fun s => connectionWeightedTangent μ (D s) - ![F s, 0])
      ((connectionTransverseMatrix μ (-y 0) (y 1) (y 2) (y 3)).mulVec
        (connectionWeightedTangent μ (D t) - ![F t, 0]) +
        ((connectionTransverseMatrix μ (-y 0) (y 1) (y 2) (y 3)).mulVec ![F t, 0] +
          ![0, μ ^ 2 * connectionWeakClockPartials (-y 0) (y 1) (y 2) (y 3) 3 / w] +
          D t 0 • connectionPhaseColumn μ y)) t := by
  have hvec : HasDerivAt (fun s => ![F s, (0 : ℝ)])
      ![connectionStrongClockPartials (-y 0) (y 1) (y 2) (y 3) 3 / w, 0] t := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · exact hF
    · exact hasDerivAt_const _ _
  have hwall : (1 / w) • connectionWallColumn μ y -
      ![connectionStrongClockPartials (-y 0) (y 1) (y 2) (y 3) 3 / w, 0] =
      ![0, μ ^ 2 * connectionWeakClockPartials (-y 0) (y 1) (y 2) (y 3) 3 / w] := by
    ext i
    fin_cases i <;> simp [connectionWallColumn, div_eq_mul_inv, mul_comm]
  apply ((hasDerivAt_connectionWeightedTangent (Y := fun _ => y) hμ hD).sub hvec).congr_deriv
  rw [hζ, Matrix.mulVec_sub]
  calc
    _ = (connectionTransverseMatrix μ (-y 0) (y 1) (y 2) (y 3)).mulVec (connectionWeightedTangent μ (D t)) +
        ((1 / w) • connectionWallColumn μ y -
          ![connectionStrongClockPartials (-y 0) (y 1) (y 2) (y 3) 3 / w, 0]) +
        D t 0 • connectionPhaseColumn μ y := by abel
    _ = _ := by rw [hwall]; abel

/-- The weak response keeps the entry amplitude after subtracting the strong-source primitive. -/
theorem connectionLog_growing_transverse_bounds {Y : ℝ → ProjectiveState} {D : ℝ → (Fin 4 → ℝ)}
    {μ a b : ℝ} (hab : a ≤ b) (hμ : 4 ≤ μ)
    (hY : ∀ z ∈ Icc a b, HasDerivAt Y (connectionLogField (Y z)) z)
    (hm : ∀ z ∈ Icc a b, |-Y z 0 - μ| ≤ 1 / 2)
    (hu : ∀ z ∈ Icc a b, 0 ≤ Y z 1 ∧ Y z 1 ≤ 1 / 10000)
    (hv : ∀ z ∈ Icc a b, 0 < Y z 2 ∧ Y z 2 ≤ 1)
    (hw : ∀ z ∈ Icc a b, 0 ≤ Y z 3 ∧ Y z 3 ≤ 1)
    (hentry : Y a 1 ≤ Y a 2) (hsmall : Y a 1 ≤ (1 / 10000) / μ) (hwall : Y a 3 ≤ 1 / 10000)
    (hw0 : 0 < Y a 3)
    (hD : ∀ z ∈ Icc a b, HasDerivAt D (connectionLogLinearizedRates (Y z) (D z)) z)
    (hζ : ∀ z ∈ Icc a b, D z 3 = 1 / Y a 3) (hx0 : D a 1 = 0) (hy0 : D a 2 = 0) :
    ∀ t ∈ Icc a b,
      |D t 1| ≤ 32 + 12800 * Y a 1 + 96 * Y t 3 ^ 2 / (μ * Y a 3) + 128 * (∫ z in a..t, |D z 0|) ∧
      |D t 2| ≤ (12800 * Y a 1 + 64 * Y t 3 ^ 2 / (μ * Y a 3) + 128 * (∫ z in a..t, |D z 0|)) / μ ^ 2 := by
  obtain ⟨F, hF0, hF, hFbound⟩ := exists_connectionGrowingPrimitive hab hμ hY hm hu hv hw hentry hw0
  have hμ0 : 0 < μ := by linarith only [hμ]
  have hcY := HasDerivAt.continuousOn hY
  have hcD := HasDerivAt.continuousOn hD
  have hcF := HasDerivAt.continuousOn hF
  have hU := continuousOn_pi.mp hcY 1
  have hweak := (continuous_connectionGrowingSources μ (Y a 3)).2.1.comp_continuousOn hcY
  have hZ := (continuousOn_pi.mp hcD 0).abs
  let R : ℝ → ℝ := fun z => 64 * μ * Y z 1 * |F z| +
    connectionGrowingWeakSource μ (Y a 3) (Y z) + 64 * |D z 0|
  have hR : ContinuousOn R (Icc a b) :=
    (((hU.const_mul (64 * μ)).mul hcF.abs).add hweak).add (hZ.const_mul 64)
  have hzero : connectionWeightedTangent μ (D a) - ![F a, 0] = 0 := by
    ext i
    fin_cases i <;> simp [connectionWeightedTangent, hx0, hy0, hF0]
  intro t ht
  have hsub : Icc a t ⊆ Icc a b := Icc_subset_Icc_right ht.2
  have H := connectionLog_transverse_forced (ξ := fun z => connectionWeightedTangent μ (D z) - ![F z, 0])
    (R := R) hab hμ hY hm hu hv hw hentry hsmall hwall ⟨le_rfl, hab⟩ ht ht.1
    (fun z hz => hasDerivAt_connectionGrowingResidual (ne_of_gt hμ0) (hD z (hsub hz)) (hF z (hsub hz)) (hζ z (hsub hz)))
    (hR.mono hsub) (fun z hz => ?_)
  · rw [hzero, norm_zero, zero_add] at H
    have h1 : IntervalIntegrable (fun z => 64 * μ * Y z 1 * |F z|) volume a t :=
      (((hU.const_mul (64 * μ)).mul hcF.abs).mono hsub).intervalIntegrable_of_Icc ht.1
    have h2 : IntervalIntegrable (fun z => connectionGrowingWeakSource μ (Y a 3) (Y z)) volume a t :=
      (hweak.mono hsub).intervalIntegrable_of_Icc ht.1
    have h3 := ((hZ.const_mul 64).mono hsub).intervalIntegrable_of_Icc (μ := volume) ht.1
    dsimp [R] at H
    rw [intervalIntegral.integral_add (h1.add h2) h3, intervalIntegral.integral_add h1 h2,
      intervalIntegral.integral_const_mul] at H
    have HF := connectionLog_growing_primitive_transfer ht.1 hμ (fun z hz => hY z (hsub hz))
      (fun z hz => hm z (hsub hz)) (fun z hz => hu z (hsub hz))
      (fun z hz => hv z (hsub hz)) (fun z hz => hw z (hsub hz)) hentry hw0
      (hcF.mono hsub) (fun z hz => hFbound z (hsub hz))
    have HW := (connectionLog_growing_source_integrals ht.1 hμ (fun z hz => hY z (hsub hz))
      (fun z hz => hm z (hsub hz)) (fun z hz => hu z (hsub hz))
      (fun z hz => hv z (hsub hz)) (fun z hz => hw z (hsub hz)) hentry hw0).2.1
    have HR : ‖connectionWeightedTangent μ (D t) - ![F t, 0]‖ ≤
        12800 * Y a 1 + 64 * Y t 3 ^ 2 / (μ * Y a 3) + 128 * (∫ z in a..t, |D z 0|) := by
      apply H.trans
      exact (mul_le_mul_of_nonneg_left (add_le_add (add_le_add HF HW) (le_refl _))
        (by norm_num : (0 : ℝ) ≤ 2)).trans_eq (by ring)
    have HC := connectionShiftedTangent_component_bounds hμ0 HR
    exact ⟨HC.1.trans ((add_le_add (hFbound t ht) (le_refl _)).trans_eq (by ring)), HC.2⟩
  · have hz' := hsub hz
    have hv' : 0 ≤ Y z 2 ∧ Y z 2 ≤ 1 := ⟨(hv z hz').1.le, (hv z hz').2⟩
    have hweak0 := (connectionGrowingSources_nonneg hμ0.le hw0.le (hu z hz').1 hv'.1 (hw z hz').1).2.1
    have hweakNorm : ‖![0, μ ^ 2 * connectionWeakClockPartials (-Y z 0) (Y z 1) (Y z 2) (Y z 3) 3 / Y a 3]‖ ≤
        connectionGrowingWeakSource μ (Y a 3) (Y z) := by
      apply (pi_norm_le_iff_of_nonempty _).mpr
      intro i
      fin_cases i
      · simpa using hweak0
      · change ‖μ ^ 2 * connectionWeakClockPartials (-Y z 0) (Y z 1) (Y z 2) (Y z 3) 3 / Y a 3‖ ≤ _
        simpa only [Real.norm_eq_abs] using
          (connectionGrowingSources_bound hμ hw0 (hm z hz') (hu z hz') hv' (hw z hz')).2.1
    apply (norm_add_le _ _).trans
    apply add_le_add
    · exact (norm_add_le _ _).trans (add_le_add
        (connectionTransverseMatrix_strong_forcing hμ (hm z hz') (hu z hz') hv' (hw z hz') (F z)) hweakNorm)
    · exact connectionPhaseColumn_forcing hμ (hm z hz') (hu z hz') hv' (hw z hz') (D z 0)

end BianchiIX
