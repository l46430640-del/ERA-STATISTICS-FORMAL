import BianchiIX.Dynamics.PartialCoreRadialVariation
import BianchiIX.Dynamics.PartialCoreMovingStart
import BianchiIX.Dynamics.CoreExitEvents
import BianchiIX.Algebra.PartialCoreResponse

noncomputable section

namespace BianchiIX

open Set

theorem partialCore_exit_factor_bound {y : ProjectiveState} {t₀ k a b : ℝ}
    (hk : 6 ≤ k) (hab : a ≤ b) (hD : 0 < projectiveStateDenom y)
    (hdom : Icc a b ⊆ normalizedMaxDomain (fromProjectiveState y) t₀)
    (hA : ∀ t ∈ Icc a b, 0 < 1 + normalizedMaxCurve (fromProjectiveState y) t₀ t 0)
    (hcore : ∀ t ∈ Icc a b, coreRegion k (projectiveOriginalFlow y t₀ t))
    (hV : projectiveOriginalFlow y t₀ b 2 = 1) (hM : projectiveOriginalFlow y t₀ b 0 < 1) :
    let β := projectiveOriginalFlow y t₀
    0 < coreExitRadialFactor (β b) ∧ coreExitRadialFactor (β b) ≤ 1 ∧
      |coreExitRadialFactor (β b) - 1| ≤ 8 * (β a 1 / k + (β a 2 * β a 3) ^ 2 / k ^ 2) := by
  intro β
  let θ := fun t => projectiveCoreAngle (β t)
  have hk0 : 0 < k := by linarith only [hk]
  have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hb : b ∈ Icc a b := ⟨hab, le_rfl⟩
  have hθ (t : ℝ) (ht : t ∈ Icc a b) : HasDerivAt θ (coreOriginalClockRate (β t)) t :=
    hasDerivAt_coreAngle_scaled (hasDerivAt_projectiveOriginalFlow_time hD (hdom ht) (hA t ht))
      (zero_lt_one.trans_le (hcore t ht).2.1)
  have hmono : MonotoneOn θ (Icc a b) := monotoneOn_of_deriv_nonneg (convex_Icc a b)
    (fun t ht => (hθ t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hθ t (interior_subset ht)).differentiableAt.differentiableWithinAt)
    (fun t ht => by
      rw [(hθ t (interior_subset ht)).deriv]
      exact (coreRegion_clock_regular hk (hcore t (interior_subset ht))).2.2.le)
  obtain ⟨hU, hP⟩ := normalized_core_prefix_contraction hk (convex_Icc a b) hdom
    (fromProjectiveState_constraint (ne_of_gt hD)) hA ha hb hab
    (fun t ht => (coreRegion_radius_bounds hk (hcore t ht)).1)
    (fun t ht => (hcore t ht).2.1)
    (fun t ht => (coreRegion_wall_bounds (hcore t ht)).1)
    (fun t ht => (coreRegion_wall_bounds (hcore t ht)).2)
  have hexp : Real.exp (-k * (θ b - θ a) / 4) ≤ 1 := Real.exp_le_one_iff.mpr
    (div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hk0.le) (sub_nonneg.mpr (hmono ha hb hab)))
      (by norm_num))
  have hUle : β b 1 ≤ β a 1 := hU.trans
    (mul_le_of_le_one_right (hcore a ha).2.2.1.1 hexp)
  change β b 2 * β b 3 ≤ β a 2 * β a 3 at hP
  change β b 2 = 1 at hV
  rw [hV, one_mul] at hP
  obtain ⟨hpos, hle, herr⟩ := coreRegion_exit_factor_bounds hk (hcore b hb) hV hM
  refine ⟨hpos, hle, herr.trans ?_⟩
  exact mul_le_mul_of_nonneg_left (add_le_add (div_le_div_of_nonneg_right hUle hk0.le)
    (div_le_div_of_nonneg_right ((sq_le_sq₀ (coreRegion_wall_bounds (hcore b hb)).2.1
      (hcore a ha).2.2.2.1).mpr hP) (sq_nonneg k))) (by norm_num)

/-- Formula (E.20) for the genuine moving-wall differential of an arbitrary core prefix. -/
theorem partialCore_wall_arrival_radius_response {y : ProjectiveState} {t₀ k a b : ℝ}
    (hk : 6 ≤ k) (hab : a ≤ b) (hD : 0 < projectiveStateDenom y)
    (hdom : Icc a b ⊆ normalizedMaxDomain (fromProjectiveState y) t₀)
    (hA : ∀ t ∈ Icc a b, 0 < 1 + normalizedMaxCurve (fromProjectiveState y) t₀ t 0)
    (hcore : ∀ t ∈ Icc a b, coreRegion k (projectiveOriginalFlow y t₀ t))
    (hR : coreRadius (projectiveOriginalFlow y t₀ a 0) (projectiveOriginalFlow y t₀ a 2) = k)
    (hV : projectiveOriginalFlow y t₀ b 2 = 1) (hM : projectiveOriginalFlow y t₀ b 0 < 1)
    (w : ProjectiveState) :
    let β := projectiveOriginalFlow y t₀
    let v := fderiv ℝ toCoreAngleState (β a) (projectiveFlowDifferential y t₀ a w)
    let dz := fderiv ℝ projectiveCoreAngle (β a) (projectiveFlowDifferential y t₀ a w)
    let U := β a 1
    let P := β a 2 * β a 3
    |(fderiv ℝ toCoreAngleState (β b) (projectiveWallArrivalDifferential y t₀ b w)) 0 - v 0| ≤
      4096 * coreVariationBound *
        (|v 1| + (U + P) * (|v 0| + |v 2|) / k + (k * U + P ^ 2 / k) * |dz|) := by
  intro β v dz U P
  let ξ := fun t => coreProjectedFlowVariation y t₀ t w
  let F := coreAngleField (projectiveCoreAngle (β a)) (toCoreAngleState (β a))
  let Q := (4 * coreVariationBound) * partialCoreVariationBudget k U P v dz
  have hk0 : 0 < k := by linarith only [hk]
  have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hb : b ∈ Icc a b := ⟨hab, le_rfl⟩
  have hQ (t : ℝ) (ht : t ∈ Icc a b) : ‖scaleCoreVariation k (ξ t)‖ ≤ Q := by
    have hsub : Icc a t ⊆ Icc a b := fun _ hs => ⟨hs.1, hs.2.trans ht.2⟩
    exact partialCore_projectedFlowVariation_bound hk ht.1 hD (fun _ hs => hdom (hsub hs))
      (fun s hs => hA s (hsub hs)) (fun s hs => hcore s (hsub hs)) hR w
  have hdrift := partialCore_projectedFlowVariation_radius_drift hk hab hD hdom hA hcore w hQ
  have hinit : ξ a = v - dz • F := rfl
  obtain ⟨hF0, hF1, _⟩ := partialCore_field_bounds hk (hcore a ha) hR
  change |F 0| ≤ 2 * (k * U + P ^ 2 / k) at hF0
  change |F 1| ≤ 2 * k * U at hF1
  have hr : |ξ a 0 - v 0| ≤ 2 * (k * U + P ^ 2 / k) * |dz| := by
    rw [hinit]
    change |(v 0 - dz * F 0) - v 0| ≤ _
    rw [sub_sub_cancel_left, abs_neg, abs_mul]
    exact (mul_le_mul_of_nonneg_left hF0 (abs_nonneg dz)).trans_eq (mul_comm _ _)
  have hx : |k * ξ a 1| ≤ k * |v 1| + 2 * k ^ 2 * U * |dz| := by
    rw [hinit]
    change |k * (v 1 - dz * F 1)| ≤ _
    rw [abs_mul, abs_of_pos hk0]
    have H := (abs_sub (v 1) (dz * F 1)).trans (add_le_add (le_refl |v 1|)
      (by simpa only [abs_mul] using mul_le_mul_of_nonneg_left hF1 (abs_nonneg dz)))
    have HH := mul_le_mul_of_nonneg_left H hk0.le
    convert! HH using 1
    ring
  obtain ⟨hs, hs1, hse⟩ := partialCore_exit_factor_bound hk hab hD hdom hA hcore hV hM
  have hsmall : U + P ≤ 1 := by
    have HU := coreBootstrap_wall_bound hk (hcore a ha).2.2.1.2
    have HP := coreBootstrap_wall_bound hk (hcore a ha).2.2.2.2
    change U ≤ 1 / 60000 at HU
    change P ≤ 1 / 60000 at HP
    linarith only [HU, HP]
  have hK : 1 ≤ coreVariationBound := Real.one_le_exp_iff.mpr (by positivity)
  have H := partial_core_radius_arrival_error hk (hcore a ha).2.2.1.1
    (hcore a ha).2.2.2.1 hsmall hK hs.le hs1 hse hr hx hdrift
  rw [(coreWallArrivalDifferential_correction hk hD (hdom hb) (hA b hb) (hcore b hb) hV hM w).2]
  exact H

end BianchiIX
