import BianchiIX.Algebra.CoreDomain
import BianchiIX.Dynamics.CoreAngle
import BianchiIX.Dynamics.ConstrainedComplete

noncomputable section

namespace BianchiIX

open Set

theorem normalized_core_chart_bounds {x : NormalizedState} {k : ℝ}
    (hk : 6 ≤ k) (hA : 1 + x 0 ≠ 0) (hc : stateConstraint x = 1) :
    let y := toProjectiveState x
    coreRadius (y 0) (y 2) ≤ 101 / 100 * k →
    0 ≤ y 2 →
    (0 ≤ y 1 ∧ y 1 ≤ (1 / 10000) / k) →
    (0 ≤ y 3 ∧ y 3 ≤ (1 / 10000) / k) →
    3 / k ^ 2 ≤ 1 + x 0 ∧ 1 + x 0 ≤ 3 := by
  intro y hr hv hu hw
  have H := coreBootstrap_inverse_scale_bounds hk hr hv hu hw
  have heq : 6 / projectiveDenom (y 0) (y 1) (y 2) (y 3) = 1 + x 0 :=
    projective_inverse_scale hA hc
  rwa [heq] at H

/-- A completed core segment has bounded duration in the original normalized time. -/
theorem projectiveOriginal_core_residence {β : ℝ → ProjectiveState} {I : Set ℝ}
    {k s t : ℝ} (hk : 6 ≤ k) (hI : Convex ℝ I)
    (hβ : ∀ u ∈ I, HasDerivAt β (projectiveOriginalField (β u)) u)
    (hr : ∀ u ∈ I, 99 / 100 * k ≤ coreRadius (β u 0) (β u 2) ∧
      coreRadius (β u 0) (β u 2) ≤ 101 / 100 * k)
    (hv : ∀ u ∈ I, 1 ≤ β u 2)
    (hu : ∀ u ∈ I, 0 ≤ β u 1 ∧ β u 1 ≤ (1 / 10000) / k)
    (hw : ∀ u ∈ I, 0 ≤ β u 3 ∧ β u 3 ≤ (1 / 10000) / k)
    (hs : s ∈ I) (ht : t ∈ I) (hst : s ≤ t) :
    (t - s) / k ≤ coreAngle (β t 0) (β t 2) - coreAngle (β s 0) (β s 2) ∧
      t - s ≤ 2 * k * Real.log (4 * k) := by
  let z := fun u => coreAngle (β u 0) (β u 2)
  let q := fun u => (6 / projectiveStateDenom (β u)) * coreRadius (β u 0) (β u 2) *
    coreClockFactor (coreRadius (β u 0) (β u 2)) (β u 1) (β u 3)
  have hz (u : ℝ) (hh : u ∈ I) : HasDerivAt z (q u) u :=
    hasDerivAt_coreAngle_scaled (hβ u hh) (lt_of_lt_of_le zero_lt_one (hv u hh))
  have hq (u : ℝ) (hh : u ∈ I) : 1 / k ≤ q u :=
    coreBootstrap_original_clock_lower hk (hr u hh) ((hv u hh).trans' zero_le_one) (hu u hh) (hw u hh)
  have H := hI.mul_sub_le_image_sub_of_le_deriv (HasDerivAt.continuousOn hz)
    (fun u hh => (hz u (interior_subset hh)).differentiableAt.differentiableWithinAt)
    (fun u hh => by rw [(hz u (interior_subset hh)).deriv]; exact hq u (interior_subset hh)) s hs t ht hst
  have H' : (t - s) / k ≤ z t - z s := by simpa only [one_div_mul_eq_div] using H
  refine ⟨H', ?_⟩
  have hzs := abs_le.mp (coreBootstrap_angle_bound hk (hr s hs).2 (hv s hs))
  have hzt := abs_le.mp (coreBootstrap_angle_bound hk (hr t ht).2 (hv t ht))
  have htime : (t - s) / k ≤ 2 * Real.log (4 * k) := by dsimp [z] at H'; linarith
  have H'' := (div_le_iff₀ (by linarith : 0 < k)).mp htime
  nlinarith

/-- No domain hypothesis is needed: the constrained Einstein flow exists at every forward time. -/
theorem normalized_core_residence {x : NormalizedState} {t₀ k s t : ℝ}
    (hc : stateConstraint x = 1) (hk : 6 ≤ k) (hs : t₀ ≤ s) (hst : s ≤ t)
    (hA : ∀ u ∈ Icc s t, 0 < 1 + normalizedMaxCurve x t₀ u 0) :
    let β := fun u => toProjectiveState (normalizedMaxCurve x t₀ u)
    (∀ u ∈ Icc s t, 99 / 100 * k ≤ coreRadius (β u 0) (β u 2) ∧
      coreRadius (β u 0) (β u 2) ≤ 101 / 100 * k) →
    (∀ u ∈ Icc s t, 1 ≤ β u 2) →
    (∀ u ∈ Icc s t, 0 ≤ β u 1 ∧ β u 1 ≤ (1 / 10000) / k) →
    (∀ u ∈ Icc s t, 0 ≤ β u 3 ∧ β u 3 ≤ (1 / 10000) / k) →
    (t - s) / k ≤ coreAngle (β t 0) (β t 2) - coreAngle (β s 0) (β s 2) ∧
      t - s ≤ 2 * k * Real.log (4 * k) := by
  intro β hr hv hu hw
  apply projectiveOriginal_core_residence hk (convex_Icc s t) ?_ hr hv hu hw ⟨le_rfl, hst⟩ ⟨hst, le_rfl⟩ hst
  intro u hh
  have H := normalizedMaxCurve_forward_of_constraint hc (hs.trans hh.1)
  exact hasDerivAt_projectiveOriginalFlow H.1 (ne_of_gt (hA u hh)) H.2.1

/-- All closed core initial data lift to the actual complete constrained flow. -/
theorem core_initial_forward_complete {y : ProjectiveState} {k : ℝ} (hk : 6 ≤ k)
    (hu : 0 ≤ y 1 ∧ y 1 ≤ (1 / 10000) / k)
    (hw : 0 ≤ y 3 ∧ y 3 ≤ (1 / 10000) / k) (t₀ : ℝ) :
    0 < 1 + fromProjectiveState y 0 ∧
      toProjectiveState (fromProjectiveState y) = y ∧
      Ici t₀ ⊆ normalizedMaxDomain (fromProjectiveState y) t₀ := by
  have hD : 0 < projectiveStateDenom y :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (coreBootstrap_denom_lower hk hu hw)
  exact ⟨fromProjectiveState_clock_pos hD, toProjectiveState_fromProjectiveState (ne_of_gt hD),
    normalizedMaxDomain_contains_Ici_of_constraint (fromProjectiveState_constraint (ne_of_gt hD)) t₀⟩

end BianchiIX
