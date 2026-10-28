import BianchiIX.Dynamics.CoreLogRateBounds
import BianchiIX.Dynamics.CoreEntryBounds

noncomputable section

namespace BianchiIX

open Set

theorem coreRegion_log_rate_bounds {k : ℝ} {y : ProjectiveState}
    (hk : 6 ≤ k) (hy : coreRegion k y) :
    let z := projectiveCoreAngle y
    let Y := toCoreAngleState y
    let J := coreLogRateJacobian z Y
    |coreLogRates z Y 0| ≤ 2 * k ∧ |coreLogRates z Y 1| ≤ 4 / k ∧
      |J 0 0| ≤ 2 ∧ |J 0 1| ≤ 4 * (1 / 10000) / k ^ 2 ∧ |J 0 2| ≤ 4 / k ∧
      |J 1 0| ≤ 8 / k ^ 2 ∧ |J 1 1| ≤ 8 ∧ |J 1 2| ≤ 8 * (1 / 10000) / k ^ 2 := by
  intro z Y J
  have hv0 : 0 < y 2 := lt_of_lt_of_le zero_lt_one hy.2.1
  have hcoord := (coreAngle_coordinates (m := y 0) hv0).1
  have hv : 1 ≤ Y 0 / Real.cosh z := by
    change 1 ≤ coreRadius (y 0) (y 2) / Real.cosh (coreAngle (y 0) (y 2))
    rw [hcoord]
    exact hy.2.1
  have hw : 0 ≤ Y 2 / (Y 0 / Real.cosh z) ∧ Y 2 / (Y 0 / Real.cosh z) ≤ (1 / 10000) / k := by
    change 0 ≤ y 2 * y 3 / (coreRadius (y 0) (y 2) / Real.cosh (coreAngle (y 0) (y 2))) ∧
      y 2 * y 3 / (coreRadius (y 0) (y 2) / Real.cosh (coreAngle (y 0) (y 2))) ≤ _
    rw [hcoord, mul_div_cancel_left₀ _ (ne_of_gt hv0)]
    exact (coreRegion_wall_bounds hy).2
  have hr := coreRegion_radius_bounds hk hy
  have hval := coreLogRates_bounds hk hr hv hy.2.2.1 hw
  exact ⟨hval.1, hval.2, coreLogRateJacobian_bounds hk hr hv hy.2.2.1 hw⟩

private theorem abs_three_row_le {a b c x y z A B C : ℝ}
    (ha : |a| ≤ A) (hb : |b| ≤ B) (hc : |c| ≤ C) :
    |a * x + b * y + c * z| ≤ A * |x| + B * |y| + C * |z| := by
  have H := (abs_add_le (a * x + b * y) (c * z)).trans
    (add_le_add (abs_add_le (a * x) (b * y)) (le_refl _))
  simp only [abs_mul] at H
  exact H.trans (add_le_add (add_le_add
    (mul_le_mul_of_nonneg_right ha (abs_nonneg _))
    (mul_le_mul_of_nonneg_right hb (abs_nonneg _)))
    (mul_le_mul_of_nonneg_right hc (abs_nonneg _)))

/-- The weak rate retains the strongly damped variation instead of replacing it by its supremum. -/
theorem coreRegion_log_rate_variation_bound {k Q : ℝ} {y : ProjectiveState} {ξ : CoreAngleState}
    (hk : 6 ≤ k) (hy : coreRegion k y) (hQ : ‖scaleCoreVariation k ξ‖ ≤ Q) :
    let D := fderiv ℝ (coreLogRates (projectiveCoreAngle y)) (toCoreAngleState y) ξ
    |D 0| ≤ 3 * Q ∧ |D 1| ≤ (9 / k ^ 2) * Q + (8 / k) * |k * ξ 1| := by
  intro D
  let J := coreLogRateJacobian (projectiveCoreAngle y) (toCoreAngleState y)
  have hk0 : 0 < k := by linarith only [hk]
  have hQ0 : 0 ≤ Q := (norm_nonneg _).trans hQ
  have hc (i : Fin 3) : |scaleCoreVariation k ξ i| ≤ Q :=
    (show |scaleCoreVariation k ξ i| ≤ ‖scaleCoreVariation k ξ‖ from
      norm_le_pi_norm (scaleCoreVariation k ξ) i).trans hQ
  have hr : |ξ 0| ≤ Q := hc 0
  have hp : |ξ 2| ≤ Q := hc 2
  have hx : k * |ξ 1| ≤ Q := by simpa only [scaleCoreVariation, Matrix.cons_val_one,
    Matrix.cons_val_zero, abs_mul, abs_of_pos hk0] using hc 1
  have hu : |ξ 1| ≤ Q := by nlinarith only [hx, hk, abs_nonneg (ξ 1)]
  have hv : 0 < y 2 := lt_of_lt_of_le zero_lt_one hy.2.1
  have hd : coreAuxiliary (projectiveCoreAngle y) (toCoreAngleState y) 1 ≠ 0 := by
    rw [coreAuxiliary_projective_clockFactor hv]
    exact ne_of_gt (coreRegion_clock_regular hk hy).2.1
  have hD : D = J.mulVec ξ := coreLogRates_fderiv _ (ne_of_gt (coreRadius_pos hv)) hd ξ
  have hrow (i : Fin 2) : D i = J i 0 * ξ 0 + J i 1 * ξ 1 + J i 2 * ξ 2 := by
    rw [hD]
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, add_assoc]
  obtain ⟨_, _, h00, h01, h02, h10, h11, h12⟩ := coreRegion_log_rate_bounds hk hy
  have hsmall : 4 * (1 / 10000 : ℝ) / k ^ 2 ≤ 1 / 100 := by
    apply (div_le_iff₀ (sq_pos_of_pos hk0)).mpr
    nlinarith only [hk]
  have hpk : 4 / k ≤ 2 / 3 := (div_le_iff₀ hk0).mpr (by linarith only [hk])
  constructor
  · rw [hrow 0]
    have H := abs_three_row_le h00 h01 h02 (x := ξ 0) (y := ξ 1) (z := ξ 2)
    have H' := H.trans (add_le_add (add_le_add
      (mul_le_mul_of_nonneg_left hr (by norm_num : (0 : ℝ) ≤ 2))
      (mul_le_mul hsmall hu (abs_nonneg _) (by norm_num)))
      (mul_le_mul hpk hp (abs_nonneg _) (by norm_num)))
    linarith only [H', hQ0]
  · rw [hrow 1]
    have H := abs_three_row_le h10 h11 h12 (x := ξ 0) (y := ξ 1) (z := ξ 2)
    have H' := H.trans (add_le_add (add_le_add
      (mul_le_mul_of_nonneg_left hr (by positivity : 0 ≤ 8 / k ^ 2)) (le_refl _))
      (mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ 8 * (1 / 10000 : ℝ) / k ^ 2)))
    apply H'.trans
    rw [abs_mul, abs_of_pos hk0]
    have hcoeff : 8 / k ^ 2 + 8 * (1 / 10000 : ℝ) / k ^ 2 ≤ 9 / k ^ 2 := by
      rw [← add_div]
      exact div_le_div_of_nonneg_right (by norm_num) (sq_nonneg k)
    have HH := mul_le_mul_of_nonneg_right hcoeff hQ0
    have heq : (8 / k) * (k * |ξ 1|) = 8 * |ξ 1| := by field_simp
    rw [heq]
    linarith only [HH]

theorem hasDerivAt_coreFlow_log_rates {y : ProjectiveState} {k t₀ t : ℝ}
    (hk : 6 ≤ k) (hD : 0 < projectiveStateDenom y)
    (ht : t ∈ normalizedMaxDomain (fromProjectiveState y) t₀)
    (hA : 0 < 1 + normalizedMaxCurve (fromProjectiveState y) t₀ t 0)
    (hy : coreRegion k (projectiveOriginalFlow y t₀ t)) :
    let β := projectiveOriginalFlow y t₀
    let Y := fun s => toCoreAngleState (β s)
    let rate := coreOriginalClockRate (β t)
    let L := coreLogRates (projectiveCoreAngle (β t)) (Y t)
    HasDerivAt (fun s => Y s 1) ((rate * L 0) * Y t 1) t ∧
      HasDerivAt (fun s => Y s 2) ((rate * L 1) * Y t 2) t := by
  intro β Y rate L
  have hv : 0 < β t 2 := lt_of_lt_of_le zero_lt_one hy.2.1
  have H := hasDerivAt_toCoreAngleState_scaled (hasDerivAt_projectiveOriginalFlow_time hD ht hA) hv
    (ne_of_gt (coreRegion_clock_regular hk hy).2.1)
  have hcoef := coreAngleField_log_rates (projectiveCoreAngle (β t)) (Y t)
  constructor
  · convert! hasDerivAt_pi.mp H 1 using 1
    change (rate * L 0) * Y t 1 = rate * coreAngleField (projectiveCoreAngle (β t)) (Y t) 1
    rw [hcoef.1]
    ring
  · convert! hasDerivAt_pi.mp H 2 using 1
    change (rate * L 1) * Y t 2 = rate * coreAngleField (projectiveCoreAngle (β t)) (Y t) 2
    rw [hcoef.2]
    ring

theorem exists_large_core_log_rate_variation {Y : CoreAngleState} (hk : 6 ≤ Y 0)
    (hu : 0 ≤ Y 1 ∧ Y 1 ≤ (1 / 10000) / Y 0)
    (hw : 0 ≤ Y 2 ∧ Y 2 ≤ (1 / 10000) / Y 0) :
    ∃ T > 0, IsLeast {t | 0 < t ∧ projectiveOriginalFlow (coreRadiusEntry Y) 0 t 2 = 1} T ∧
      ∀ v : CoreAngleState, ∀ t ∈ Icc 0 T,
        let β := projectiveOriginalFlow (coreRadiusEntry Y) 0
        let ξ := coreProjectedFlowVariation (coreRadiusEntry Y) 0 t (fderiv ℝ coreRadiusEntry Y v)
        let Q := (2 * coreVariationBound) * (|v 0| + Y 0 * |v 1| + |v 2|)
        let D := fderiv ℝ (coreLogRates (projectiveCoreAngle (β t))) (toCoreAngleState (β t)) ξ
        |D 0| ≤ 3 * Q ∧ |D 1| ≤ (9 / Y 0 ^ 2) * Q + (8 / Y 0) * |Y 0 * ξ 1| := by
  obtain ⟨T, hT, hfirst, hcore, hnorm⟩ := exists_large_core_entry_variation hk hu hw
  exact ⟨T, hT, hfirst, fun v t ht => coreRegion_log_rate_variation_bound hk (hcore t ht) (hnorm t ht v)⟩

end BianchiIX
