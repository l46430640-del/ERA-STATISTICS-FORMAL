import BianchiIX.Dynamics.PartialCoreDownwardBounds
import BianchiIX.Dynamics.PartialCoreLogDerivativeBounds
import BianchiIX.Dynamics.PartialCoreMultiplierFormula

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

/-- The fixed downward return has positive C1 multipliers with the bounds (E.23), also at V = 1. -/
theorem partialCoreDownwardReturn_multiplier_response {k : ℝ} {y : ProjectiveState}
    (hk : 6 ≤ k) (hy : coreRegion k y) (hR : coreRadius (y 0) (y 2) = k)
    (hV : 1 < y 2 ∨ (y 2 = 1 ∧ 1 ≤ y 0)) :
    let τ := partialCoreDownwardReturnTime
    (∀ᶠ x in 𝓝 y,
      projectiveOriginalFlow x 0 (τ x) 1 = x 1 * partialCoreReturnMultiplier τ x 0 ∧
      projectiveOriginalFlow x 0 (τ x) 3 = (x 2 * x 3) * partialCoreReturnMultiplier τ x 1) ∧
    (∀ i : Fin 2, 0 < partialCoreReturnMultiplier τ y i ∧
      ContDiffAt ℝ 1 (fun x => Real.log (partialCoreReturnMultiplier τ x i)) y ∧
      ContDiffAt ℝ 1 (fun x => partialCoreReturnMultiplier τ x i) y) ∧
    ∀ w : ProjectiveState,
      let dz := fderiv ℝ projectiveCoreAngle y w
      let Q₀ := partialCoreVariationBudget k (y 1) (y 2 * y 3)
        (fderiv ℝ toCoreAngleState y w) dz
      |fderiv ℝ (fun x => Real.log (partialCoreReturnMultiplier τ x 0)) y w| ≤
        40 * coreVariationBound * Real.log (4 * k) * Q₀ + 2 * k * |dz| ∧
      |fderiv ℝ (fun x => Real.log (partialCoreReturnMultiplier τ x 1)) y w| ≤
        236 * coreVariationBound * Real.log (4 * k) * Q₀ / k ^ 2 + 4 * |dz| / k := by
  intro τ
  have hD := (coreRegion_clock_regular hk hy).1
  have HR := partialCoreDownwardReturn_regular hk hy hR hV
  have HB := partialCoreDownwardReturn_bounds hk hy hR hV
  have hnorm := partialCoreDownwardReturn_variation hk hy hR hV
  have hpos : 0 < τ y := HR.1.1.1
  have hcτ : ContDiffAt ℝ 1 τ y := HR.2.1.of_le (by norm_num)
  have hnear := HR.2.2.2.1
  have hbase := hnear.self_of_nhds
  have hdom : Icc 0 (τ y) ⊆ normalizedMaxDomain (fromProjectiveState y) 0 :=
    fun t ht => (hbase.2 t ht).1
  have hA : ∀ t ∈ Icc 0 (τ y), 0 < 1 + normalizedMaxCurve (fromProjectiveState y) 0 t 0 :=
    fun t ht => (hbase.2 t ht).2
  have hcore : ∀ t ∈ Icc 0 (τ y), coreRegion k (projectiveOriginalFlow y 0 t) :=
    fun t ht => (HB.2.2 t ht).2.1
  have hhit : ∀ᶠ x in 𝓝 y, projectiveOriginalFlow x 0 (τ x) 2 = 1 :=
    hnear.mono fun _ h => h.1.1.2.2.1
  have hformula := eventually_partialCore_multiplier_formula hk hD hcτ.continuousAt hpos
    (hnear.mono fun _ h => h.2) hcore hhit
  refine ⟨hformula, ?_, ?_⟩
  · intro i
    exact ⟨coreFlowMultiplier_pos _ _ _ _ i,
      contDiffAt_log_partialCoreReturnMultiplier hk hD hcτ hpos.le hdom hA hcore i,
      contDiffAt_partialCoreReturnMultiplier hk hD hcτ hpos.le hdom hA hcore i⟩
  · intro w dz Q₀
    have H := partialCoreReturn_log_derivative_bounds hk hD hcτ hpos.le hdom hA hcore hhit HB.1 w
      (fun t ht => hnorm t ht w)
    exact ⟨H.1.trans_eq (by ring), H.2.trans_eq (by ring)⟩

end BianchiIX
