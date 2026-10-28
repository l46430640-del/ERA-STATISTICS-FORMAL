import BianchiIX.Analysis.ClockEnvelope
import BianchiIX.Dynamics.CoreStrongVariation

noncomputable section

namespace BianchiIX

open Set MeasureTheory

theorem coreProjectedFlowVariation_strong_integrals {y : ProjectiveState} {t₀ k a b Q : ℝ}
    (hk : 6 ≤ k) (hab : a ≤ b) (hD : 0 < projectiveStateDenom y)
    (hdom : Icc a b ⊆ normalizedMaxDomain (fromProjectiveState y) t₀)
    (hA : ∀ t ∈ Icc a b, 0 < 1 + normalizedMaxCurve (fromProjectiveState y) t₀ t 0)
    (hcore : ∀ t ∈ Icc a b, coreRegion k (projectiveOriginalFlow y t₀ t))
    (hentry : Real.cosh (projectiveCoreAngle (projectiveOriginalFlow y t₀ a)) = k)
    (w : ProjectiveState)
    (hQ : ∀ t ∈ Icc a b, ‖scaleCoreVariation k (coreProjectedFlowVariation y t₀ t w)‖ ≤ Q) :
    let θ := fun t => projectiveCoreAngle (projectiveOriginalFlow y t₀ t)
    let rate := fun t => coreOriginalClockRate (projectiveOriginalFlow y t₀ t)
    let x := fun t => k * coreProjectedFlowVariation y t₀ t w 1
    (∫ t in a..b, (|x t| / Real.cosh (θ t)) * rate t) ≤
        (12 * |x a| + 432 * projectiveOriginalFlow y t₀ a 1 * Q) / k ^ 2 ∧
      (∫ t in a..b, |x t| * rate t) ≤
        (4 * |x a| + 48 * projectiveOriginalFlow y t₀ a 1 * Q) / k := by
  intro θ rate x
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
  exact core_clock_forced_variation_integrals hk hab (hcore a ⟨le_rfl, hab⟩).2.2.1.1 hQ0 hx hθ hrate
    (fun t ht => (coreRegion_clock_regular hk (hcore t ht)).2.2.le) hentry
    (coreProjectedFlowVariation_strong_bound hk hab hD hdom hA hcore w hQ)

/-- Both estimates in (B.36) for every actual large-core traversal, including zero-wall entrances. -/
theorem exists_large_core_strong_integrals {Y : CoreAngleState} (hk : 6 ≤ Y 0)
    (hu : 0 ≤ Y 1 ∧ Y 1 ≤ (1 / 10000) / Y 0)
    (hw : 0 ≤ Y 2 ∧ Y 2 ≤ (1 / 10000) / Y 0) :
    ∃ T > 0, IsLeast {t | 0 < t ∧ projectiveOriginalFlow (coreRadiusEntry Y) 0 t 2 = 1} T ∧
      ∀ v : CoreAngleState,
        let y := coreRadiusEntry Y
        let w := fderiv ℝ coreRadiusEntry Y v
        let θ := fun t => projectiveCoreAngle (projectiveOriginalFlow y 0 t)
        let rate := fun t => coreOriginalClockRate (projectiveOriginalFlow y 0 t)
        let x := fun t => Y 0 * coreProjectedFlowVariation y 0 t w 1
        let Q := (2 * coreVariationBound) * (|v 0| + Y 0 * |v 1| + |v 2|)
        (∫ t in 0..T, (|x t| / Real.cosh (θ t)) * rate t) ≤ (12 * |x 0| + 432 * Y 1 * Q) / Y 0 ^ 2 ∧
          (∫ t in 0..T, |x t| * rate t) ≤ (4 * |x 0| + 48 * Y 1 * Q) / Y 0 := by
  have hD : 0 < projectiveStateDenom (coreRadiusEntry Y) :=
    (coreRegion_clock_regular hk (coreRadiusEntry_region hk hu hw)).1
  have hc : stateConstraint (fromProjectiveState (coreRadiusEntry Y)) = 1 := fromProjectiveState_constraint (ne_of_gt hD)
  obtain ⟨T, hT, hfirst, hcore, _⟩ := exists_large_core_traversal hk hu hw
  obtain ⟨S, _, hfirstS, _, hnorm⟩ := exists_large_core_entry_variation hk hu hw
  have hST : S = T := hfirstS.unique hfirst
  subst S
  have hentry : Real.cosh (projectiveCoreAngle (projectiveOriginalFlow (coreRadiusEntry Y) 0 0)) = Y 0 := by
    rw [projectiveOriginalFlow_initial hD, projectiveCoreAngle,
      cosh_coreAngle (show 0 < coreRadiusEntry Y 2 by change (0 : ℝ) < 1; norm_num),
      coreRadius_coreRadiusEntry (by linarith only [hk] : 1 < Y 0)]
    exact div_one _
  refine ⟨T, hT, hfirst, ?_⟩
  intro v y w θ rate x Q
  have H := coreProjectedFlowVariation_strong_integrals hk hT.le hD
    (fun s hs => normalizedMaxDomain_contains_Ici_of_constraint hc 0 hs.1)
    (fun s hs => (hcore s hs).1) (fun s hs => (hcore s hs).2) hentry w
    (fun s hs => hnorm s hs v)
  rw [projectiveOriginalFlow_initial hD] at H
  exact H

end BianchiIX
