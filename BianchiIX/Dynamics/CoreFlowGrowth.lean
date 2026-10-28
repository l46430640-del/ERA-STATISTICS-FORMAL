import BianchiIX.Dynamics.CoreFlowVariation
import BianchiIX.Dynamics.CoreVariationGrowth
import BianchiIX.Dynamics.LargeCoreReturn

noncomputable section

namespace BianchiIX

open Set

theorem signedRowSum_smul_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} {c : ℝ} (hc : 0 ≤ c) (i : ι) :
    signedRowSum (c • A) i = c * signedRowSum A i := by
  simp only [signedRowSum, Matrix.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg hc]
  rw [← Finset.mul_sum, ← mul_add]

theorem coreRegion_clock_regular {k : ℝ} {y : ProjectiveState}
    (hk : 6 ≤ k) (hy : coreRegion k y) :
    0 < projectiveStateDenom y ∧
      0 < coreClockFactor (coreRadius (y 0) (y 2)) (y 1) (y 3) ∧
        0 < coreOriginalClockRate y := by
  have hk0 : 0 < k := by linarith only [hk]
  have hr := coreRegion_radius_bounds hk hy
  obtain ⟨hu, hw⟩ := coreRegion_wall_bounds hy
  have hD := coreBootstrap_denom_lower (m := y 0) (v := y 2) hk hu hw
  have hd := (coreBootstrap_clock_bounds hk hr.1 hu hw).1
  have hrate := coreBootstrap_original_clock_lower hk hr (zero_le_one.trans hy.2.1) hu hw
  exact ⟨lt_of_lt_of_le (by norm_num) hD, lt_of_lt_of_le (by norm_num) hd,
    lt_of_lt_of_le (one_div_pos.mpr hk0) hrate⟩

theorem coreRegion_weighted_signedRowSum {k : ℝ} {y : ProjectiveState}
    (hk : 6 ≤ k) (hy : coreRegion k y) (i : Fin 3) :
    signedRowSum (coreWeightedJacobian k (projectiveCoreAngle y) (toCoreAngleState y)) i ≤
      2 / Real.cosh (projectiveCoreAngle y) + 24 * ((1 / 10000) / k) := by
  obtain ⟨h0, h1, h2⟩ := coreRegion_variational_row_sums hk hy
  have hb : 0 ≤ 2 / Real.cosh (projectiveCoreAngle y) + 24 * ((1 / 10000) / k) := by
    have hk0 : 0 < k := by linarith only [hk]
    positivity
  have hfin : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := by decide
  dsimp only [projectiveCoreAngle] at hb ⊢
  fin_cases i <;> simp [signedRowSum, hfin] <;> linarith only [h0, h1, h2, hb]

/-- The comparison can be made in original time, without differentiating an inverse clock. -/
theorem coreClockProjection_growth {beta v : ℝ → ProjectiveState} {k a b : ℝ}
    (hk : 6 ≤ k) (hab : a ≤ b)
    (hbeta : ∀ t ∈ Icc a b, HasDerivAt beta (projectiveOriginalField (beta t)) t)
    (hv : ∀ t ∈ Icc a b, HasDerivAt v (fderiv ℝ projectiveOriginalField (beta t) (v t)) t)
    (hregion : ∀ t ∈ Icc a b, coreRegion k (beta t)) :
    ‖scaleCoreVariation k (coreClockProjection (beta b) (v b))‖ ≤
      ‖scaleCoreVariation k (coreClockProjection (beta a) (v a))‖ * coreVariationBound := by
  have hk0 : 0 < k := by linarith only [hk]
  let xi := fun t => coreClockProjection (beta t) (v t)
  let theta := fun t => projectiveCoreAngle (beta t)
  let rate := fun t => coreOriginalClockRate (beta t)
  let f := fun t => scaleCoreVariation k (xi t)
  let A := fun t => rate t • coreWeightedJacobian k (theta t) (toCoreAngleState (beta t))
  have hxi (t : ℝ) (ht : t ∈ Icc a b) : HasDerivAt xi
      (rate t • (coreAngleJacobian (theta t) (toCoreAngleState (beta t))).mulVec (xi t)) t := by
    obtain ⟨hD, hd, _⟩ := coreRegion_clock_regular hk (hregion t ht)
    exact hasDerivAt_coreClockProjection (hbeta t ht) (hv t ht)
      (lt_of_lt_of_le zero_lt_one (hregion t ht).2.1) (ne_of_gt hD) (ne_of_gt hd)
  have hf (t : ℝ) (ht : t ∈ Icc a b) : HasDerivAt f ((A t).mulVec (f t)) t := by
    dsimp only [A, f]
    rw [Matrix.smul_mulVec, coreWeightedJacobian_mulVec (ne_of_gt hk0)]
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · exact hasDerivAt_pi.mp (hxi t ht) 0
    · apply ((hasDerivAt_pi.mp (hxi t ht) 1).const_mul k).congr_deriv
      change k * (rate t * _) = rate t * (k * _)
      ring
    · exact hasDerivAt_pi.mp (hxi t ht) 2
  have htheta (t : ℝ) (ht : t ∈ Icc a b) : HasDerivAt theta (rate t) t := by
    exact hasDerivAt_coreAngle_scaled (hbeta t ht) (lt_of_lt_of_le zero_lt_one (hregion t ht).2.1)
  have hZ (t : ℝ) (ht : t ∈ Icc a b) :
      HasDerivAt (fun s => coreGrowthPrimitive k (theta s))
        ((2 / Real.cosh (theta t) + 24 * ((1 / 10000) / k)) * rate t) t :=
    (hasDerivAt_coreGrowthPrimitive k (theta t)).comp t (htheta t ht)
  have H := norm_le_exp_of_signedRowSum
    (fun t ht => (hf t ht).continuousAt.continuousWithinAt)
    (fun t ht => hf t (Ico_subset_Icc_self ht))
    (fun t ht => (hZ t ht).continuousAt.continuousWithinAt)
    (fun t ht => hZ t (Ico_subset_Icc_self ht))
    (fun t ht i => by
      have ht' := Ico_subset_Icc_self ht
      have hrate := (coreRegion_clock_regular hk (hregion t ht')).2.2.le
      dsimp only [A]
      rw [signedRowSum_smul_nonneg hrate]
      exact (mul_le_mul_of_nonneg_left (coreRegion_weighted_signedRowSum hk (hregion t ht') i)
        hrate).trans_eq (mul_comm _ _)) b ⟨hab, le_rfl⟩
  have hangle (t : ℝ) (ht : t ∈ Icc a b) : |theta t| ≤ Real.log (4 * k) :=
    coreBootstrap_angle_bound hk (coreRegion_radius_bounds hk (hregion t ht)).2 (hregion t ht).2.1
  exact H.trans (mul_le_mul_of_nonneg_left
    (coreGrowthPrimitive_exp_difference hk (hangle a ⟨le_rfl, hab⟩) (hangle b ⟨hab, le_rfl⟩))
    (norm_nonneg _))

/-- Uniform control of the actual flow differential after projection to fixed angle. -/
theorem coreProjectedFlowVariation_growth {y : ProjectiveState} {t₀ k a b : ℝ}
    (hk : 6 ≤ k) (hab : a ≤ b) (hD : 0 < projectiveStateDenom y)
    (hdomain : Icc a b ⊆ normalizedMaxDomain (fromProjectiveState y) t₀)
    (hA : ∀ t ∈ Icc a b, 0 < 1 + normalizedMaxCurve (fromProjectiveState y) t₀ t 0)
    (hregion : ∀ t ∈ Icc a b, coreRegion k (projectiveOriginalFlow y t₀ t)) (w : ProjectiveState) :
    ‖scaleCoreVariation k (coreProjectedFlowVariation y t₀ b w)‖ ≤
      ‖scaleCoreVariation k (coreProjectedFlowVariation y t₀ a w)‖ * coreVariationBound := by
  exact coreClockProjection_growth (beta := projectiveOriginalFlow y t₀)
    (v := fun s => projectiveFlowDifferential y t₀ s w) hk hab
    (fun t ht => hasDerivAt_projectiveOriginalFlow_time hD (hdomain ht) (hA t ht))
    (fun t ht => hasDerivAt_projectiveFlowDifferential_apply hD (hdomain ht) (hA t ht) w) hregion

/-- Every admissible large-core entrance has a first return and a uniform projected derivative bound. -/
theorem exists_large_core_projected_growth {k u w : ℝ} (hk : 6 ≤ k)
    (hu : 0 ≤ u ∧ u ≤ (1 / 10000) / k) (hw : 0 ≤ w ∧ w ≤ (1 / 10000) / k) :
    let y : ProjectiveState := ![1 + Real.sqrt (k ^ 2 - 1), u, 1, w]
    ∃ T > 0,
      IsLeast {t | 0 < t ∧ projectiveOriginalFlow y 0 t 2 = 1} T ∧
      (∀ t ∈ Icc 0 T, 0 < 1 + normalizedMaxCurve (fromProjectiveState y) 0 t 0 ∧
        coreRegion k (projectiveOriginalFlow y 0 t)) ∧
      ∀ t ∈ Icc 0 T, ∀ v : ProjectiveState,
        ‖scaleCoreVariation k (coreProjectedFlowVariation y 0 t v)‖ ≤
          ‖scaleCoreVariation k (coreClockProjection y v)‖ * coreVariationBound := by
  intro y
  have hD : 0 < projectiveStateDenom y :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (coreBootstrap_denom_lower hk hu hw)
  have hc : stateConstraint (fromProjectiveState y) = 1 := fromProjectiveState_constraint (ne_of_gt hD)
  obtain ⟨T, hT, hfirst, hcore, _⟩ := exists_large_core_traversal hk hu hw
  refine ⟨T, hT, hfirst, hcore, ?_⟩
  intro t ht v
  have hsub : Icc 0 t ⊆ Icc 0 T := fun _ hs => ⟨hs.1, hs.2.trans ht.2⟩
  have H := coreProjectedFlowVariation_growth hk ht.1 hD
    (fun s hs => normalizedMaxDomain_contains_Ici_of_constraint hc 0 hs.1)
    (fun s hs => (hcore s (hsub hs)).1) (fun s hs => (hcore s (hsub hs)).2) v
  rw [coreProjectedFlowVariation_initial hD] at H
  exact H

end BianchiIX
