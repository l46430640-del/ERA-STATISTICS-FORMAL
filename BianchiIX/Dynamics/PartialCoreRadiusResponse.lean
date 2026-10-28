import BianchiIX.Dynamics.PartialCoreExitVariation
import BianchiIX.Dynamics.PartialCoreEntryVariation
import BianchiIX.Dynamics.PartialCoreEvents

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

/-- The ordinary C2 first-return map from every interior core entrance satisfies (E.20). -/
theorem exists_partialCore_radius_response {k : ℝ} {y : ProjectiveState}
    (hk : 6 ≤ k) (hy : coreRegion k y) (hR : coreRadius (y 0) (y 2) = k)
    (hV : 1 < y 2) :
    ∃ T > 0, IsLeast {t | 0 < t ∧ projectiveOriginalFlow y 0 t 2 = 1} T ∧
      ∃ τ : ProjectiveState → ℝ, τ y = T ∧ ContDiffAt ℝ 2 τ y ∧
        (∀ᶠ z in 𝓝 y,
          IsLeast {t | 0 < t ∧ t ∈ normalizedMaxDomain (fromProjectiveState z) 0 ∧
            projectiveOriginalFlow z 0 t 2 = 1} (τ z) ∧
          ∀ t ∈ Icc 0 (τ z), t ∈ normalizedMaxDomain (fromProjectiveState z) 0 ∧
            0 < 1 + normalizedMaxCurve (fromProjectiveState z) 0 t 0) ∧
        let F := fun z => toCoreAngleState (projectiveOriginalFlow z 0 (τ z))
        ContDiffAt ℝ 2 F y ∧ ∀ w : ProjectiveState,
          let v := fderiv ℝ toCoreAngleState y w
          let dz := fderiv ℝ projectiveCoreAngle y w
          |(fderiv ℝ F y w) 0 - v 0| ≤ 4096 * coreVariationBound *
            (|v 1| + (y 1 + y 2 * y 3) * (|v 0| + |v 2|) / k +
              (k * y 1 + (y 2 * y 3) ^ 2 / k) * |dz|) := by
  have hD := (coreRegion_clock_regular hk hy).1
  have hc := fromProjectiveState_constraint (ne_of_gt hD)
  let x := fromProjectiveState y
  let β := projectiveOriginalFlow y 0
  have hzero : β 0 = y := projectiveOriginalFlow_initial hD 0
  have hA0 : 0 < 1 + normalizedMaxCurve x 0 0 0 := by
    rw [normalizedMaxCurve_initial]
    exact fromProjectiveState_clock_pos hD
  have hR0 : coreRadius (β 0 0) (β 0 2) = k := by rw [hzero]; exact hR
  have hV0 : 1 < β 0 2 := by rw [hzero]; exact hV
  have hU0 : 0 ≤ β 0 1 ∧ β 0 1 ≤ (1 / 10000) / k := by rw [hzero]; exact hy.2.2.1
  have hP0 : 0 ≤ β 0 2 * β 0 3 ∧ β 0 2 * β 0 3 ≤ (1 / 10000) / k := by
    rw [hzero]
    exact hy.2.2.2
  obtain ⟨T, hT, hfirst, hreg, _⟩ := exists_partialCore_entry_variation hk hy hR hV
  obtain ⟨S, hS, σ, hσ, hcσ, hcP, _, hdP, hnear⟩ :=
    exists_normalized_partialCore_firstReturn_two hc hk le_rfl hA0 hR0 hV0 hU0 hP0
  have hbase := hnear.self_of_nhds
  rw [hσ] at hbase
  have hfirstS : IsLeast {t | 0 < t ∧ β t 2 = 1} S := by
    refine ⟨⟨hS, hbase.1.1.2.2⟩, ?_⟩
    intro t ht
    exact hbase.1.2 ⟨ht.1, normalizedMaxDomain_contains_Ici_of_constraint hc 0 ht.1.le, ht.2⟩
  have hST : S = T := hfirstS.unique hfirst
  rw [hST] at hσ hdP
  have htm : T ∈ Icc 0 T := ⟨hT.le, le_rfl⟩
  have hdown := normalized_core_return_downward hc hk le_rfl hT (hreg T htm).1 hfirst.1.2
    (fun t ht => (hreg t ⟨ht.1.le, ht.2.le⟩).2.2.1)
    (coreRegion_radius_bounds hk (hreg T htm).2).1
    (coreRegion_wall_bounds (hreg T htm).2).1 (coreRegion_wall_bounds (hreg T htm).2).2
  let τ := fun z => σ (fromProjectiveState z)
  let P := fun z => projectiveOriginalFlow z 0 (τ z)
  let F := fun z => toCoreAngleState (P z)
  have hτ : τ y = T := hσ
  have hfrom := contDiffAt_fromProjectiveState 2 (ne_of_gt hD)
  have hcτ : ContDiffAt ℝ 2 τ y := hcσ.comp y hfrom
  have hcP' : ContDiffAt ℝ 2 P y := by
    convert! hcP.comp y hfrom using 1
  have hdP' : HasFDerivAt P (projectiveWallArrivalDifferential y 0 T) y := by
    convert! hdP.comp y ((hfrom.differentiableAt (by norm_num)).hasFDerivAt) using 1
  have hPt : P y = β T := by change projectiveOriginalFlow y 0 (τ y) = β T; rw [hτ]
  have hv : 0 < P y 2 := by rw [hPt]; exact zero_lt_one.trans_le (hreg T htm).2.2.1
  have hcCoord := contDiffAt_toCoreAngleState 2 hv
  have hcF : ContDiffAt ℝ 2 F y := hcCoord.comp y hcP'
  have hdF : HasFDerivAt F
      ((fderiv ℝ toCoreAngleState (β T)).comp (projectiveWallArrivalDifferential y 0 T)) y := by
    have H := (hcCoord.differentiableAt (by norm_num)).hasFDerivAt.comp y hdP'
    rw [hPt] at H
    exact H
  refine ⟨T, hT, hfirst, τ, hτ, hcτ, ?_, hcF, ?_⟩
  · filter_upwards [hfrom.continuousAt.tendsto.eventually hnear] with z hz
    exact ⟨hz.1, hz.2.1⟩
  intro w v dz
  have H := partialCore_wall_arrival_radius_response hk hT.le hD
    (fun t ht => normalizedMaxDomain_contains_Ici_of_constraint hc 0 ht.1)
    (fun t ht => (hreg t ht).1) (fun t ht => (hreg t ht).2) hR0 hfirst.1.2 hdown.1 w
  dsimp only at H
  rw [projectiveOriginalFlow_initial hD, projectiveFlowDifferential_initial hD,
    ContinuousLinearMap.id_apply] at H
  rw [hdF.fderiv, ContinuousLinearMap.comp_apply]
  exact H

end BianchiIX
