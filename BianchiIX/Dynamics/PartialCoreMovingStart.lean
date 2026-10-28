import BianchiIX.Dynamics.PartialCoreFieldBounds
import BianchiIX.Dynamics.CoreAngleArrival

noncomputable section

namespace BianchiIX

open Set

def partialCoreVariationBudget (k u p : ℝ) (v : CoreAngleState) (dz : ℝ) : ℝ :=
  |v 0| + k * |v 1| + |v 2| + (k ^ 2 * u + p / k) * |dz|

/-- Moving the initial angle changes the fixed-angle initial tangent by the angular field. -/
theorem partialCore_moving_start_bound {k : ℝ} {y : ProjectiveState}
    (hk : 6 ≤ k) (hy : coreRegion k y) (hR : coreRadius (y 0) (y 2) = k)
    (v : CoreAngleState) (dz : ℝ) :
    ‖scaleCoreVariation k
      (v - dz • coreAngleField (projectiveCoreAngle y) (toCoreAngleState y))‖ ≤
      4 * partialCoreVariationBudget k (y 1) (y 2 * y 3) v dz := by
  have hk0 : 0 < k := by linarith only [hk]
  let N := |v 0| + k * |v 1| + |v 2|
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hv : ‖scaleCoreVariation k v‖ ≤ N := by
    apply (pi_norm_le_iff_of_nonempty _).mpr
    intro i
    fin_cases i
    · change |v 0| ≤ N
      dsimp [N]
      linarith only [mul_nonneg hk0.le (abs_nonneg (v 1)), abs_nonneg (v 2)]
    · change |k * v 1| ≤ N
      rw [abs_mul, abs_of_pos hk0]
      dsimp [N]
      linarith only [abs_nonneg (v 0), abs_nonneg (v 2)]
    · change |v 2| ≤ N
      dsimp [N]
      linarith only [abs_nonneg (v 0), mul_nonneg hk0.le (abs_nonneg (v 1))]
  have hfield := partialCore_weighted_field_bound hk hy hR
  rw [← scaleCoreVariationLinear_apply, map_sub, map_smul]
  calc
    _ ≤ ‖scaleCoreVariationLinear k v‖ +
        ‖dz • scaleCoreVariationLinear k
          (coreAngleField (projectiveCoreAngle y) (toCoreAngleState y))‖ := norm_sub_le _ _
    _ = ‖scaleCoreVariation k v‖ + |dz| *
        ‖scaleCoreVariation k (coreAngleField (projectiveCoreAngle y) (toCoreAngleState y))‖ := by
      rw [norm_smul, Real.norm_eq_abs, scaleCoreVariationLinear_apply, scaleCoreVariationLinear_apply]
    _ ≤ N + |dz| * (4 * (k ^ 2 * y 1 + (y 2 * y 3) / k)) :=
      add_le_add hv (mul_le_mul_of_nonneg_left hfield (abs_nonneg _))
    _ ≤ _ := by unfold partialCoreVariationBudget; dsimp [N] at hN ⊢; nlinarith only [hN]

/-- The correction is an identity for ordinary derivatives of a projective initial curve. -/
theorem coreClockProjection_curve {y : ℝ → ProjectiveState} {w : ProjectiveState}
    {r dz : ℝ} {v : CoreAngleState} (hy : HasDerivAt y w r) (hv : 0 < y r 2)
    (hY : HasDerivAt (fun s => toCoreAngleState (y s)) v r)
    (hz : HasDerivAt (fun s => projectiveCoreAngle (y s)) dz r) :
    coreClockProjection (y r) w =
      v - dz • coreAngleField (projectiveCoreAngle (y r)) (toCoreAngleState (y r)) := by
  have hY' := ((contDiffAt_toCoreAngleState 1 hv).differentiableAt
    (by norm_num)).hasFDerivAt.comp_hasDerivAt r hy
  have hz' := ((contDiffAt_projectiveCoreAngle 1 hv).differentiableAt
    (by norm_num)).hasFDerivAt.comp_hasDerivAt r hy
  rw [coreClockProjection, hY'.unique hY, hz'.unique hz]

/-- Ordinary parameter derivatives of the exact flow give the same fixed-angle variation. -/
theorem coreProjectedFlowVariation_curve {y : ℝ → ProjectiveState} {w : ProjectiveState}
    {r t₀ t : ℝ} (hy : HasDerivAt y w r) (hD : 0 < projectiveStateDenom (y r))
    (ht : t ∈ normalizedMaxDomain (fromProjectiveState (y r)) t₀)
    (hA : 0 < 1 + normalizedMaxCurve (fromProjectiveState (y r)) t₀ t 0)
    (hV : 0 < projectiveOriginalFlow (y r) t₀ t 2) :
    coreProjectedFlowVariation (y r) t₀ t w =
      deriv (fun s => toCoreAngleState (projectiveOriginalFlow (y s) t₀ t)) r -
        deriv (fun s => projectiveCoreAngle (projectiveOriginalFlow (y s) t₀ t)) r •
          coreAngleField (projectiveCoreAngle (projectiveOriginalFlow (y r) t₀ t))
            (toCoreAngleState (projectiveOriginalFlow (y r) t₀ t)) := by
  have hflow := (hasFDerivAt_projectiveOriginalFlow_initial hD ht hA).comp_hasDerivAt r hy
  have hY := ((contDiffAt_toCoreAngleState 1 hV).differentiableAt
    (by norm_num)).hasFDerivAt.comp_hasDerivAt r hflow
  have hz := ((contDiffAt_projectiveCoreAngle 1 hV).differentiableAt
    (by norm_num)).hasFDerivAt.comp_hasDerivAt r hflow
  change HasDerivAt (fun s => toCoreAngleState (projectiveOriginalFlow (y s) t₀ t)) _ r at hY
  change HasDerivAt (fun s => projectiveCoreAngle (projectiveOriginalFlow (y s) t₀ t)) _ r at hz
  rw [hY.deriv, hz.deriv]
  rfl

theorem partialCore_clockProjection_bound {k : ℝ} {y : ProjectiveState}
    (hk : 6 ≤ k) (hy : coreRegion k y) (hR : coreRadius (y 0) (y 2) = k)
    (w : ProjectiveState) :
    ‖scaleCoreVariation k (coreClockProjection y w)‖ ≤
      4 * partialCoreVariationBudget k (y 1) (y 2 * y 3)
        (fderiv ℝ toCoreAngleState y w) (fderiv ℝ projectiveCoreAngle y w) :=
  partialCore_moving_start_bound hk hy hR _ _

/-- Any exact core prefix, including a prefix starting in its interior, obeys the same budget. -/
theorem partialCore_moving_variation_growth {beta v : ℝ → ProjectiveState} {k a b : ℝ}
    (hk : 6 ≤ k) (hab : a ≤ b)
    (hbeta : ∀ t ∈ Icc a b, HasDerivAt beta (projectiveOriginalField (beta t)) t)
    (hv : ∀ t ∈ Icc a b, HasDerivAt v (fderiv ℝ projectiveOriginalField (beta t) (v t)) t)
    (hregion : ∀ t ∈ Icc a b, coreRegion k (beta t))
    (hR : coreRadius (beta a 0) (beta a 2) = k) :
    ‖scaleCoreVariation k (coreClockProjection (beta b) (v b))‖ ≤
      4 * coreVariationBound * partialCoreVariationBudget k (beta a 1) (beta a 2 * beta a 3)
        (fderiv ℝ toCoreAngleState (beta a) (v a))
        (fderiv ℝ projectiveCoreAngle (beta a) (v a)) := by
  have H := coreClockProjection_growth hk hab hbeta hv hregion
  have H0 := partialCore_clockProjection_bound hk (hregion a ⟨le_rfl, hab⟩) hR (v a)
  have hC : 0 ≤ coreVariationBound := (Real.exp_pos _).le
  exact H.trans ((mul_le_mul_of_nonneg_right H0 hC).trans_eq (by ring))

/-- Applied to the differential of the exact Einstein flow; no tangent equation is assumed. -/
theorem partialCore_projectedFlowVariation_bound {y : ProjectiveState} {t₀ k a b : ℝ}
    (hk : 6 ≤ k) (hab : a ≤ b) (hD : 0 < projectiveStateDenom y)
    (hdomain : Icc a b ⊆ normalizedMaxDomain (fromProjectiveState y) t₀)
    (hA : ∀ t ∈ Icc a b, 0 < 1 + normalizedMaxCurve (fromProjectiveState y) t₀ t 0)
    (hregion : ∀ t ∈ Icc a b, coreRegion k (projectiveOriginalFlow y t₀ t))
    (hR : coreRadius (projectiveOriginalFlow y t₀ a 0) (projectiveOriginalFlow y t₀ a 2) = k)
    (w : ProjectiveState) :
    let beta := projectiveOriginalFlow y t₀
    let v := projectiveFlowDifferential y t₀ a w
    ‖scaleCoreVariation k (coreProjectedFlowVariation y t₀ b w)‖ ≤
      4 * coreVariationBound * partialCoreVariationBudget k (beta a 1) (beta a 2 * beta a 3)
        (fderiv ℝ toCoreAngleState (beta a) v) (fderiv ℝ projectiveCoreAngle (beta a) v) := by
  exact partialCore_moving_variation_growth (beta := projectiveOriginalFlow y t₀)
    (v := fun t => projectiveFlowDifferential y t₀ t w) hk hab
    (fun t ht => hasDerivAt_projectiveOriginalFlow_time hD (hdomain ht) (hA t ht))
    (fun t ht => hasDerivAt_projectiveFlowDifferential_apply hD (hdomain ht) (hA t ht) w)
    hregion hR

end BianchiIX
