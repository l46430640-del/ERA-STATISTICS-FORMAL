import BianchiIX.Analysis.ConnectionStrongForcing
import BianchiIX.Dynamics.ConnectionForcedGrowth
import BianchiIX.Dynamics.ConnectionMoments

noncomputable section

namespace BianchiIX

open Set MeasureTheory

theorem hasDerivAt_connectionShiftedTangent {D : ℝ → (Fin 4 → ℝ)} {y : ProjectiveState} {μ t : ℝ}
    (hμ : μ ≠ 0) (hD : HasDerivAt D (connectionLogLinearizedRates y (D t)) t)
    (hz : D t 3 = 0) (x : ℝ) :
    HasDerivAt (fun s => connectionWeightedTangent μ (D s) - ![x, 0])
      ((connectionTransverseMatrix μ (-y 0) (y 1) (y 2) (y 3)).mulVec
        (connectionWeightedTangent μ (D t) - ![x, 0]) +
        ((connectionTransverseMatrix μ (-y 0) (y 1) (y 2) (y 3)).mulVec ![x, 0] +
          D t 0 • connectionPhaseColumn μ y)) t := by
  have H := (hasDerivAt_connectionWeightedTangent (Y := fun _ => y) hμ hD).sub_const ![x, 0]
  apply H.congr_deriv
  rw [hz, zero_smul, add_zero, Matrix.mulVec_sub]
  abel

/-- Subtracting the constant entry vector makes the strong initial singularity integrable against U. -/
theorem connectionLog_shifted_variation_bound {Y : ℝ → ProjectiveState} {D : ℝ → (Fin 4 → ℝ)}
    {μ a b x : ℝ} (hab : a ≤ b) (hμ : 4 ≤ μ)
    (hY : ∀ z ∈ Icc a b, HasDerivAt Y (connectionLogField (Y z)) z)
    (hm : ∀ z ∈ Icc a b, |-Y z 0 - μ| ≤ 1 / 2)
    (hu : ∀ z ∈ Icc a b, 0 ≤ Y z 1 ∧ Y z 1 ≤ 1 / 10000)
    (hv : ∀ z ∈ Icc a b, 0 < Y z 2 ∧ Y z 2 ≤ 1)
    (hw : ∀ z ∈ Icc a b, 0 ≤ Y z 3 ∧ Y z 3 ≤ 1)
    (hentry : Y a 1 ≤ Y a 2) (hsmall : Y a 1 ≤ (1 / 10000) / μ) (hwall : Y a 3 ≤ 1 / 10000)
    (hD : ∀ z ∈ Icc a b, HasDerivAt D (connectionLogLinearizedRates (Y z) (D z)) z)
    (hζ : ∀ z ∈ Icc a b, D z 3 = 0) (hx0 : D a 1 = x) (hy0 : D a 2 = 0)
    {t : ℝ} (ht : t ∈ Icc a b) :
    ‖connectionWeightedTangent μ (D t) - ![x, 0]‖ ≤
      256 * Y a 1 * |x| + 128 * ∫ z in a..t, |D z 0| := by
  have hμ0 : 0 < μ := by linarith only [hμ]
  have hsub : Icc a t ⊆ Icc a b := Icc_subset_Icc_right ht.2
  have hcY := HasDerivAt.continuousOn hY
  have hcD := HasDerivAt.continuousOn hD
  let R : ℝ → ℝ := fun z => (64 * μ * |x|) * Y z 1 + 64 * |D z 0|
  have hR : ContinuousOn R (Icc a t) :=
    (((continuousOn_pi.mp hcY 1).const_mul _).add ((continuousOn_pi.mp hcD 0).abs.const_mul 64)).mono hsub
  have H := connectionLog_transverse_forced (ξ := fun z => connectionWeightedTangent μ (D z) - ![x, 0])
    (R := R) hab hμ hY hm hu hv hw hentry hsmall hwall ⟨le_rfl, hab⟩ ht ht.1
    (fun z hz => hasDerivAt_connectionShiftedTangent (ne_of_gt hμ0) (hD z (hsub hz)) (hζ z (hsub hz)) x)
    hR (fun z hz => ?_)
  · have hzero : connectionWeightedTangent μ (D a) - ![x, 0] = 0 := by
      ext i
      fin_cases i <;> simp [connectionWeightedTangent, hx0, hy0]
    rw [hzero, norm_zero, zero_add] at H
    have hU := ((continuousOn_pi.mp hcY 1).mono hsub).intervalIntegrable_of_Icc (μ := volume) ht.1
    have hZ := ((continuousOn_pi.mp hcD 0).abs.mono hsub).intervalIntegrable_of_Icc (μ := volume) ht.1
    dsimp [R] at H
    rw [intervalIntegral.integral_add (hU.const_mul _) (hZ.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at H
    have HM := (connectionLog_dissipative_moments ht.1 hμ (fun z hz => hY z (hsub hz))
      (fun z hz => hm z (hsub hz)) (fun z hz => hu z (hsub hz))
      (fun z hz => hv z (hsub hz)) (fun z hz => hw z (hsub hz)) hentry).1
    apply H.trans
    apply (mul_le_mul_of_nonneg_left (add_le_add
      (mul_le_mul_of_nonneg_left HM (by positivity : 0 ≤ 64 * μ * |x|)) (le_refl _)) (by norm_num : (0 : ℝ) ≤ 2)).trans_eq
    field_simp
    ring
  · have hz' := hsub hz
    have hv' : 0 ≤ Y z 2 ∧ Y z 2 ≤ 1 := ⟨(hv z hz').1.le, (hv z hz').2⟩
    apply (norm_add_le _ _).trans
    exact (add_le_add (connectionTransverseMatrix_strong_forcing hμ (hm z hz') (hu z hz') hv' (hw z hz') x)
      (connectionPhaseColumn_forcing hμ (hm z hz') (hu z hz') hv' (hw z hz') (D z 0))).trans_eq (by dsimp [R]; ring)

end BianchiIX
