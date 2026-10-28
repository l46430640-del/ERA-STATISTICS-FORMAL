import BianchiIX.Analysis.PartialCoreVariationIntegral
import BianchiIX.Dynamics.CoreStrongVariation

noncomputable section

namespace BianchiIX

open Set MeasureTheory

/-- Strong variation is integrable on every actual core prefix, including interior entrances. -/
theorem partialCore_projectedFlowVariation_strong_integral {y : ProjectiveState} {t₀ k a b Q : ℝ}
    (hk : 6 ≤ k) (hab : a ≤ b) (hD : 0 < projectiveStateDenom y)
    (hdom : Icc a b ⊆ normalizedMaxDomain (fromProjectiveState y) t₀)
    (hA : ∀ t ∈ Icc a b, 0 < 1 + normalizedMaxCurve (fromProjectiveState y) t₀ t 0)
    (hcore : ∀ t ∈ Icc a b, coreRegion k (projectiveOriginalFlow y t₀ t))
    (w : ProjectiveState)
    (hQ : ∀ t ∈ Icc a b, ‖scaleCoreVariation k (coreProjectedFlowVariation y t₀ t w)‖ ≤ Q) :
    let rate := fun t => coreOriginalClockRate (projectiveOriginalFlow y t₀ t)
    let x := fun t => k * coreProjectedFlowVariation y t₀ t w 1
    (∫ t in a..b, |x t| * rate t) ≤
      (4 * |x a| + 48 * projectiveOriginalFlow y t₀ a 1 * Q) / k := by
  intro rate x
  let θ := fun t => projectiveCoreAngle (projectiveOriginalFlow y t₀ t)
  have hQ0 : 0 ≤ Q := (norm_nonneg _).trans (hQ a ⟨le_rfl, hab⟩)
  have hV (t : ℝ) (ht : t ∈ Icc a b) : 0 < projectiveOriginalFlow y t₀ t 2 :=
    lt_of_lt_of_le zero_lt_one (hcore t ht).2.1
  have hflow (t : ℝ) (ht : t ∈ Icc a b) := hasDerivAt_projectiveOriginalFlow_time hD (hdom ht) (hA t ht)
  have hθ (t : ℝ) (ht : t ∈ Icc a b) : HasDerivAt θ (rate t) t :=
    hasDerivAt_coreAngle_scaled (hflow t ht) (hV t ht)
  have hrate : ContinuousOn rate (Icc a b) := by
    intro t ht
    exact ((contDiffAt_coreOriginalClockRate 1 (hV t ht)
      (ne_of_gt (coreRegion_clock_regular hk (hcore t ht)).1)).continuousAt.comp
        (hflow t ht).continuousAt).continuousWithinAt
  have hx : ContinuousOn x (Icc a b) := by
    intro t ht
    have H := hasDerivAt_coreProjectedFlowVariation hD (hdom ht) (hA t ht) (hV t ht)
      (ne_of_gt (coreRegion_clock_regular hk (hcore t ht)).2.1) w
    exact ((hasDerivAt_pi.mp H 1).const_mul k).continuousAt.continuousWithinAt
  exact partial_core_clock_variation_integral hk hab (hcore a ⟨le_rfl, hab⟩).2.2.1.1 hQ0 hx hθ hrate
    (fun t ht => (coreRegion_clock_regular hk (hcore t ht)).2.2.le)
    (coreProjectedFlowVariation_strong_bound hk hab hD hdom hA hcore w hQ)

end BianchiIX
