import BianchiIX.Dynamics.PartialCoreMovingStart
import BianchiIX.Dynamics.PartialCoreFirstReturn

noncomputable section

namespace BianchiIX

open Set

/-- Every admissible interior entrance has a genuine first exit and the moving-start bound. -/
theorem exists_partialCore_entry_variation {k : ℝ} {y : ProjectiveState}
    (hk : 6 ≤ k) (hy : coreRegion k y) (hR : coreRadius (y 0) (y 2) = k)
    (hV : 1 < y 2) :
    ∃ T > 0, IsLeast {t | 0 < t ∧ projectiveOriginalFlow y 0 t 2 = 1} T ∧
      (∀ t ∈ Icc 0 T, 0 < 1 + normalizedMaxCurve (fromProjectiveState y) 0 t 0 ∧
        coreRegion k (projectiveOriginalFlow y 0 t)) ∧
      ∀ t ∈ Icc 0 T, ∀ w : ProjectiveState,
        ‖scaleCoreVariation k (coreProjectedFlowVariation y 0 t w)‖ ≤
          4 * coreVariationBound * partialCoreVariationBudget k (y 1) (y 2 * y 3)
            (fderiv ℝ toCoreAngleState y w) (fderiv ℝ projectiveCoreAngle y w) := by
  have hk0 : 0 < k := by linarith only [hk]
  have hD := (coreRegion_clock_regular hk hy).1
  have hc := fromProjectiveState_constraint (ne_of_gt hD)
  let beta := projectiveOriginalFlow y 0
  have hzero : beta 0 = y := projectiveOriginalFlow_initial hD 0
  have hA : 0 < 1 + normalizedMaxCurve (fromProjectiveState y) 0 0 0 := by
    rw [normalizedMaxCurve_initial]
    exact fromProjectiveState_clock_pos hD
  have hR0 : coreRadius (beta 0 0) (beta 0 2) = k := by rw [hzero]; exact hR
  have hV0 : 1 < beta 0 2 ∨ (beta 0 2 = 1 ∧ 1 ≤ beta 0 0) := by
    rw [hzero]
    exact Or.inl hV
  have hU0 : 0 ≤ beta 0 1 ∧ beta 0 1 ≤ (1 / 10000) / k := by
    rw [hzero]
    exact hy.2.2.1
  have hP0 : 0 ≤ beta 0 2 * beta 0 3 ∧ beta 0 2 * beta 0 3 ≤ (1 / 10000) / k := by
    rw [hzero]
    exact hy.2.2.2
  obtain ⟨T, hT, hfirst, _, _, _, _, H⟩ :=
    exists_normalized_partialCore_firstReturn hc hk le_rfl hA hR0 hV0 hU0 hP0
  have hreg (t : ℝ) (ht : t ∈ Icc 0 T) :
      0 < 1 + normalizedMaxCurve (fromProjectiveState y) 0 t 0 ∧ coreRegion k (beta t) :=
    ⟨lt_of_lt_of_le (by positivity : 0 < 3 / (2 * k ^ 2)) (H t ht).1, (H t ht).2.1⟩
  refine ⟨T, hT, hfirst, hreg, ?_⟩
  intro t ht w
  have hsub : Icc 0 t ⊆ Icc 0 T := fun _ hs => ⟨hs.1, hs.2.trans ht.2⟩
  have Hg := partialCore_projectedFlowVariation_bound hk ht.1 hD
    (fun s hs => normalizedMaxDomain_contains_Ici_of_constraint hc 0 hs.1)
    (fun s hs => (hreg s (hsub hs)).1) (fun s hs => (hreg s (hsub hs)).2) hR0 w
  dsimp only at Hg
  rw [projectiveOriginalFlow_initial hD, projectiveFlowDifferential_initial hD,
    ContinuousLinearMap.id_apply] at Hg
  exact Hg

end BianchiIX
