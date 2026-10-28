import BianchiIX.Dynamics.PartialCoreDownwardReturn
import BianchiIX.Dynamics.PartialCoreMovingStart

noncomputable section

namespace BianchiIX

open Set

/-- The fixed downward return retains the full base-orbit bounds at the incoming boundary. -/
theorem partialCoreDownwardReturn_bounds {k : ℝ} {y : ProjectiveState}
    (hk : 6 ≤ k) (hy : coreRegion k y) (hR : coreRadius (y 0) (y 2) = k)
    (hV : 1 < y 2 ∨ (y 2 = 1 ∧ 1 ≤ y 0)) :
    let T := partialCoreDownwardReturnTime y
    projectiveOriginalFlow y 0 T 0 < 1 ∧ T ≤ 2 * k * Real.log (4 * k) ∧
      ∀ t ∈ Icc 0 T,
        0 < 1 + normalizedMaxCurve (fromProjectiveState y) 0 t 0 ∧
        coreRegion k (projectiveOriginalFlow y 0 t) ∧
        |coreRadius (projectiveOriginalFlow y 0 t 0) (projectiveOriginalFlow y 0 t 2) - k| ≤
          16 * (y 1 + (y 2 * y 3) ^ 2 / k) ∧
        |coreRadius (projectiveOriginalFlow y 0 t 0) (projectiveOriginalFlow y 0 t 2) ^ 2 - k ^ 2| < 1 / 16 := by
  intro T
  have hk0 : 0 < k := by linarith only [hk]
  have hD := (coreRegion_clock_regular hk hy).1
  have hc := fromProjectiveState_constraint hD.ne'
  let β := projectiveOriginalFlow y 0
  have hzero : β 0 = y := projectiveOriginalFlow_initial hD 0
  have hA : 0 < 1 + normalizedMaxCurve (fromProjectiveState y) 0 0 0 := by
    rw [normalizedMaxCurve_initial]
    exact fromProjectiveState_clock_pos hD
  have hR0 : coreRadius (β 0 0) (β 0 2) = k := by rw [hzero]; exact hR
  have hV0 : 1 < β 0 2 ∨ (β 0 2 = 1 ∧ 1 ≤ β 0 0) := by rw [hzero]; exact hV
  have hU0 : 0 ≤ β 0 1 ∧ β 0 1 ≤ (1 / 10000) / k := by rw [hzero]; exact hy.2.2.1
  have hP0 : 0 ≤ β 0 2 * β 0 3 ∧ β 0 2 * β 0 3 ≤ (1 / 10000) / k := by
    rw [hzero]; exact hy.2.2.2
  obtain ⟨S, _, hfirstS, hM, _, _, htime, H⟩ :=
    exists_normalized_partialCore_firstReturn hc hk le_rfl hA hR0 hV0 hU0 hP0
  have hST : S = T := hfirstS.unique (partialCoreDownwardReturn_regular hk hy hR hV).1
  rw [hST] at hM htime H
  refine ⟨hM, by simpa only [sub_zero] using htime, ?_⟩
  intro t ht
  have Ht := H t ht
  change _ ∧ _ ∧ |coreRadius (β t 0) (β t 2) - k| ≤
    16 * (β 0 1 + (β 0 2 * β 0 3) ^ 2 / k) ∧ _ at Ht
  rw [hzero] at Ht
  exact ⟨lt_of_lt_of_le (by positivity : 0 < 3 / (2 * k ^ 2)) Ht.1, Ht.2⟩

/-- Moving-start variation estimates hold up to the same fixed downward return, including V = 1. -/
theorem partialCoreDownwardReturn_variation {k : ℝ} {y : ProjectiveState}
    (hk : 6 ≤ k) (hy : coreRegion k y) (hR : coreRadius (y 0) (y 2) = k)
    (hV : 1 < y 2 ∨ (y 2 = 1 ∧ 1 ≤ y 0)) :
    ∀ t ∈ Icc 0 (partialCoreDownwardReturnTime y), ∀ w : ProjectiveState,
      ‖scaleCoreVariation k (coreProjectedFlowVariation y 0 t w)‖ ≤
        4 * coreVariationBound * partialCoreVariationBudget k (y 1) (y 2 * y 3)
          (fderiv ℝ toCoreAngleState y w) (fderiv ℝ projectiveCoreAngle y w) := by
  have hD := (coreRegion_clock_regular hk hy).1
  have hc := fromProjectiveState_constraint hD.ne'
  have H := (partialCoreDownwardReturn_bounds hk hy hR hV).2.2
  have hR0 : coreRadius (projectiveOriginalFlow y 0 0 0) (projectiveOriginalFlow y 0 0 2) = k := by
    rw [projectiveOriginalFlow_initial hD]; exact hR
  intro t ht w
  have hsub : Icc 0 t ⊆ Icc 0 (partialCoreDownwardReturnTime y) := fun _ hs => ⟨hs.1, hs.2.trans ht.2⟩
  have Hg := partialCore_projectedFlowVariation_bound hk ht.1 hD
    (fun s hs => normalizedMaxDomain_contains_Ici_of_constraint hc 0 hs.1)
    (fun s hs => (H s (hsub hs)).1) (fun s hs => (H s (hsub hs)).2.1) hR0 w
  dsimp only at Hg
  rw [projectiveOriginalFlow_initial hD, projectiveFlowDifferential_initial hD,
    ContinuousLinearMap.id_apply] at Hg
  exact Hg

end BianchiIX
