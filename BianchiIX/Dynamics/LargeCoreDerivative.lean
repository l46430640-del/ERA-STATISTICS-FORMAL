import BianchiIX.Dynamics.CoreAngleArrival

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

/-- Actual fixed-angle arrival derivatives throughout every admissible large-core traversal. -/
theorem exists_large_core_angle_arrivals {k u w : ℝ} (hk : 6 ≤ k)
    (hu : 0 ≤ u ∧ u ≤ (1 / 10000) / k) (hw : 0 ≤ w ∧ w ≤ (1 / 10000) / k) :
    let y : ProjectiveState := ![1 + Real.sqrt (k ^ 2 - 1), u, 1, w]
    ∃ T > 0,
      IsLeast {t | 0 < t ∧ projectiveOriginalFlow y 0 t 2 = 1} T ∧
      (∀ t ∈ Icc 0 T, 0 < 1 + normalizedMaxCurve (fromProjectiveState y) 0 t 0 ∧
        coreRegion k (projectiveOriginalFlow y 0 t)) ∧
      ∀ a ∈ Icc 0 T, ∀ b ∈ Icc a T,
        let z := projectiveCoreAngle (projectiveOriginalFlow y 0 a)
        let Y := toCoreAngleState (projectiveOriginalFlow y 0 a)
        ∃ τ : CoreAngleState → ℝ, τ Y = b ∧ ContDiffAt ℝ 1 τ Y ∧
        (∀ᶠ X in 𝓝 Y, τ X ∈ normalizedMaxDomain (fromProjectiveState (fromCoreAngleState z X)) a ∧
          0 < 1 + normalizedMaxCurve (fromProjectiveState (fromCoreAngleState z X)) a (τ X) 0 ∧
          0 < projectiveOriginalFlow (fromCoreAngleState z X) a (τ X) 2 ∧
          projectiveCoreAngle (projectiveOriginalFlow (fromCoreAngleState z X) a (τ X)) =
            projectiveCoreAngle (projectiveOriginalFlow y 0 b)) ∧
        (∀ᶠ q : CoreAngleState × ℝ in 𝓝 (Y, b),
          q.2 ∈ normalizedMaxDomain (fromProjectiveState (fromCoreAngleState z q.1)) a ∧
          (projectiveCoreAngle (projectiveOriginalFlow (fromCoreAngleState z q.1) a q.2) =
            projectiveCoreAngle (projectiveOriginalFlow y 0 b) ↔ τ q.1 = q.2)) ∧
        ContDiffAt ℝ 1 (fun X => toCoreAngleState (projectiveOriginalFlow (fromCoreAngleState z X) a (τ X))) Y ∧
        ‖(scaleCoreVariationLinear k).comp
          ((fderiv ℝ (fun X => toCoreAngleState (projectiveOriginalFlow (fromCoreAngleState z X) a (τ X))) Y).comp
            (scaleCoreVariationLinear k⁻¹))‖ ≤ coreVariationBound := by
  intro y
  have hD : 0 < projectiveStateDenom y :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (coreBootstrap_denom_lower hk hu hw)
  have hc : stateConstraint (fromProjectiveState y) = 1 := fromProjectiveState_constraint (ne_of_gt hD)
  obtain ⟨T, hT, hfirst, hcore, _⟩ := exists_large_core_traversal hk hu hw
  refine ⟨T, hT, hfirst, hcore, ?_⟩
  intro a ha b hb z Y
  have hdom0 (s : ℝ) (hs : 0 ≤ s) : s ∈ normalizedMaxDomain (fromProjectiveState y) 0 :=
    normalizedMaxDomain_contains_Ici_of_constraint hc 0 hs
  have hsub : Icc a b ⊆ Icc 0 T := fun _ hs => ⟨ha.1.trans hs.1, hs.2.trans hb.2⟩
  have hV : 0 < projectiveOriginalFlow y 0 a 2 := lt_of_lt_of_le zero_lt_one (hcore a ha).2.2.1
  have hr : 0 < Y 0 := coreRadius_pos hV
  have hchart : fromCoreAngleState z Y = projectiveOriginalFlow y 0 a :=
    fromCoreAngleState_toCoreAngleState hV
  have hxchart : fromProjectiveState (fromCoreAngleState z Y) = normalizedMaxCurve (fromProjectiveState y) 0 a := by
    rw [hchart]
    exact fromProjectiveState_toProjectiveState (ne_of_gt (hcore a ha).1)
      ((normalizedMaxCurve_constraint (hdom0 a ha.1)).trans hc)
  have hD' : 0 < projectiveStateDenom (fromCoreAngleState z Y) := by
    rw [hchart]
    exact (coreRegion_clock_regular hk (hcore a ha).2).1
  have hdom : Icc a b ⊆ normalizedMaxDomain (fromProjectiveState (fromCoreAngleState z Y)) a := by
    rw [hxchart, normalizedMaxDomain_rebase (hdom0 a ha.1)]
    exact fun s hs => hdom0 s (hsub hs).1
  have hcurve (s : ℝ) (hs : s ∈ Icc a b) :
      normalizedMaxCurve (fromProjectiveState (fromCoreAngleState z Y)) a s =
        normalizedMaxCurve (fromProjectiveState y) 0 s := by
    rw [hxchart]
    exact normalizedMaxCurve_rebase (hdom0 a ha.1) (hdom0 s (hsub hs).1)
  have hflow (s : ℝ) (hs : s ∈ Icc a b) :
      projectiveOriginalFlow (fromCoreAngleState z Y) a s = projectiveOriginalFlow y 0 s := by
    unfold projectiveOriginalFlow
    rw [hcurve s hs]
  have hA : ∀ s ∈ Icc a b,
      0 < 1 + normalizedMaxCurve (fromProjectiveState (fromCoreAngleState z Y)) a s 0 := by
    intro s hs
    rw [hcurve s hs]
    exact (hcore s (hsub hs)).1
  have hregion : ∀ s ∈ Icc a b, coreRegion k (projectiveOriginalFlow (fromCoreAngleState z Y) a s) := by
    intro s hs
    rw [hflow s hs]
    exact (hcore s (hsub hs)).2
  simpa only [hflow b ⟨hb.1, le_rfl⟩] using exists_coreAngle_arrival_bound hk hr hb.1 hD' hdom hA hregion

end BianchiIX
