import BianchiIX.Analysis.SignedRowGrowth
import BianchiIX.Analysis.CoreGrowthBudget
import BianchiIX.Dynamics.CoreRowSums

noncomputable section

namespace BianchiIX

open Set

theorem coreWeightedJacobian_signedRowSum {k z : ℝ} {y : CoreAngleState}
    (hk : 6 ≤ k) (hr : 99 / 100 * k ≤ y 0 ∧ y 0 ≤ 101 / 100 * k)
    (hv : 1 ≤ y 0 / Real.cosh z)
    (hu : 0 ≤ y 1 ∧ y 1 ≤ (1 / 10000) / k)
    (hw : 0 ≤ y 2 / (y 0 / Real.cosh z) ∧ y 2 / (y 0 / Real.cosh z) ≤ (1 / 10000) / k)
    (hp : y 2 ≤ (1 / 10000) / k) (i : Fin 3) :
    signedRowSum (coreWeightedJacobian k z y) i ≤ 2 / Real.cosh z + 24 * ((1 / 10000) / k) := by
  obtain ⟨h0, h1, h2⟩ := coreWeightedJacobian_row_sums hk hr hv hu hw hp
  have hb : 0 ≤ 2 / Real.cosh z + 24 * ((1 / 10000) / k) := by
    have hk0 : 0 < k := by linarith
    positivity
  have hfin : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := by decide
  fin_cases i <;> simp [signedRowSum, hfin] <;> linarith only [h0, h1, h2, hb]

/-- Uniform growth for every solution of the exact core tangent equation. -/
theorem coreAngle_variation_growth {Y ξ : ℝ → CoreAngleState} {k z₀ a b : ℝ}
    (hk : 6 ≤ k) (hab : a ≤ b)
    (hξ : ∀ z ∈ Icc a b, HasDerivAt ξ ((coreAngleJacobian (z + z₀) (Y z)).mulVec (ξ z)) z)
    (hr : ∀ z ∈ Icc a b, 99 / 100 * k ≤ Y z 0 ∧ Y z 0 ≤ 101 / 100 * k)
    (hv : ∀ z ∈ Icc a b, 1 ≤ Y z 0 / Real.cosh (z + z₀))
    (hu : ∀ z ∈ Icc a b, 0 ≤ Y z 1 ∧ Y z 1 ≤ (1 / 10000) / k)
    (hw : ∀ z ∈ Icc a b, 0 ≤ Y z 2 / (Y z 0 / Real.cosh (z + z₀)) ∧
      Y z 2 / (Y z 0 / Real.cosh (z + z₀)) ≤ (1 / 10000) / k)
    (hp : ∀ z ∈ Icc a b, Y z 2 ≤ (1 / 10000) / k)
    (ha : |a + z₀| ≤ Real.log (4 * k)) (hb : |b + z₀| ≤ Real.log (4 * k)) :
    ‖scaleCoreVariation k (ξ b)‖ ≤ ‖scaleCoreVariation k (ξ a)‖ * coreVariationBound := by
  have hk0 : 0 < k := by linarith
  let f := fun z => scaleCoreVariation k (ξ z)
  let A := fun z => coreWeightedJacobian k (z + z₀) (Y z)
  have hf (z : ℝ) (hz : z ∈ Icc a b) : HasDerivAt f ((A z).mulVec (f z)) z := by
    dsimp only [A, f]
    rw [coreWeightedJacobian_mulVec (ne_of_gt hk0)]
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · exact hasDerivAt_pi.mp (hξ z hz) 0
    · exact (hasDerivAt_pi.mp (hξ z hz) 1).const_mul k
    · exact hasDerivAt_pi.mp (hξ z hz) 2
  have hZ (z : ℝ) : HasDerivAt (fun s => coreGrowthPrimitive k (s + z₀))
      (2 / Real.cosh (z + z₀) + 24 * ((1 / 10000) / k)) z := by
    convert! (hasDerivAt_coreGrowthPrimitive k (z + z₀)).comp z ((hasDerivAt_id z).add_const z₀) using 1
    simp
  have H := norm_le_exp_of_signedRowSum
    (fun z hz => (hf z hz).continuousAt.continuousWithinAt)
    (fun z hz => hf z (Ico_subset_Icc_self hz))
    (fun z _ => (hZ z).continuousAt.continuousWithinAt)
    (fun z _ => hZ z)
    (fun z hz i => coreWeightedJacobian_signedRowSum hk (hr z (Ico_subset_Icc_self hz))
      (hv z (Ico_subset_Icc_self hz)) (hu z (Ico_subset_Icc_self hz))
      (hw z (Ico_subset_Icc_self hz)) (hp z (Ico_subset_Icc_self hz)) i) b ⟨hab, le_rfl⟩
  exact H.trans (mul_le_mul_of_nonneg_left (coreGrowthPrimitive_exp_difference hk ha hb) (norm_nonneg _))

theorem coreRegion_variation_growth {β : ℝ → ProjectiveState} {ξ : ℝ → CoreAngleState}
    {k z₀ a b : ℝ} (hk : 6 ≤ k) (hab : a ≤ b)
    (hβ : ∀ z ∈ Icc a b, coreRegion k (β z))
    (hangle : ∀ z ∈ Icc a b, coreAngle (β z 0) (β z 2) = z + z₀)
    (hξ : ∀ z ∈ Icc a b, HasDerivAt ξ
      ((coreAngleJacobian (z + z₀) (toCoreAngleState (β z))).mulVec (ξ z)) z) :
    ‖scaleCoreVariation k (ξ b)‖ ≤ ‖scaleCoreVariation k (ξ a)‖ * coreVariationBound := by
  have hvpos (z : ℝ) (hz : z ∈ Icc a b) : 0 < β z 2 := lt_of_lt_of_le zero_lt_one (hβ z hz).2.1
  have hcoord (z : ℝ) (hz : z ∈ Icc a b) :
      coreRadius (β z 0) (β z 2) / Real.cosh (z + z₀) = β z 2 := by
    rw [← hangle z hz]
    exact (coreAngle_coordinates (hvpos z hz)).1
  have hbound (z : ℝ) (hz : z ∈ Icc a b) : |z + z₀| ≤ Real.log (4 * k) := by
    rw [← hangle z hz]
    exact coreBootstrap_angle_bound hk (coreRegion_radius_bounds hk (hβ z hz)).2 (hβ z hz).2.1
  apply coreAngle_variation_growth hk hab hξ
  · exact fun z hz => coreRegion_radius_bounds hk (hβ z hz)
  · intro z hz
    change 1 ≤ coreRadius (β z 0) (β z 2) / Real.cosh (z + z₀)
    rw [hcoord z hz]
    exact (hβ z hz).2.1
  · exact fun z hz => (hβ z hz).2.2.1
  · intro z hz
    change 0 ≤ β z 2 * β z 3 / (coreRadius (β z 0) (β z 2) / Real.cosh (z + z₀)) ∧
      β z 2 * β z 3 / (coreRadius (β z 0) (β z 2) / Real.cosh (z + z₀)) ≤ (1 / 10000) / k
    rw [hcoord z hz, mul_div_cancel_left₀ _ (ne_of_gt (hvpos z hz))]
    exact (coreRegion_wall_bounds (hβ z hz)).2
  · exact fun z hz => (hβ z hz).2.2.2.2
  · exact hbound a ⟨le_rfl, hab⟩
  · exact hbound b ⟨hab, le_rfl⟩

end BianchiIX
