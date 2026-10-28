import BianchiIX.Dynamics.PartialCoreLogDerivativeBounds
import BianchiIX.Dynamics.PartialCoreMultiplierFormula
import BianchiIX.Dynamics.PartialCoreRadiusResponse

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

/-- Ordinary first-return multipliers satisfy (E.23), including either zero wall. -/
theorem exists_partialCore_multiplier_response {k : ℝ} {y : ProjectiveState}
    (hk : 6 ≤ k) (hy : coreRegion k y) (hR : coreRadius (y 0) (y 2) = k)
    (hV : 1 < y 2) :
    ∃ τ : ProjectiveState → ℝ, 0 < τ y ∧ ContDiffAt ℝ 2 τ y ∧
      (∀ᶠ x in 𝓝 y,
        IsLeast {t | 0 < t ∧ t ∈ normalizedMaxDomain (fromProjectiveState x) 0 ∧
          projectiveOriginalFlow x 0 t 2 = 1} (τ x) ∧
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
  have hD := (coreRegion_clock_regular hk hy).1
  have hc := fromProjectiveState_constraint (ne_of_gt hD)
  obtain ⟨T, hT, hfirst, τ, hτ, hcτ, hnear, _⟩ := exists_partialCore_radius_response hk hy hR hV
  obtain ⟨S, _, hfirstS, hreg, hnorm⟩ := exists_partialCore_entry_variation hk hy hR hV
  have hST : S = T := hfirstS.unique hfirst
  rw [hST] at hreg hnorm
  have hpos : 0 < τ y := hτ ▸ hT
  have hdom : Icc 0 (τ y) ⊆ normalizedMaxDomain (fromProjectiveState y) 0 :=
    fun t ht => normalizedMaxDomain_contains_Ici_of_constraint hc 0 ht.1
  have hA : ∀ t ∈ Icc 0 (τ y), 0 < 1 + normalizedMaxCurve (fromProjectiveState y) 0 t 0 :=
    fun t ht => (hreg t (hτ ▸ ht)).1
  have hcore : ∀ t ∈ Icc 0 (τ y), coreRegion k (projectiveOriginalFlow y 0 t) :=
    fun t ht => (hreg t (hτ ▸ ht)).2
  have htm : T ∈ Icc 0 T := ⟨hT.le, le_rfl⟩
  have hdown := normalized_core_return_downward hc hk le_rfl hT (hreg T htm).1 hfirst.1.2
    (fun t ht => (hreg t ⟨ht.1.le, ht.2.le⟩).2.2.1)
    (coreRegion_radius_bounds hk (hreg T htm).2).1
    (coreRegion_wall_bounds (hreg T htm).2).1 (coreRegion_wall_bounds (hreg T htm).2).2
  have hM : projectiveOriginalFlow y 0 (τ y) 0 < 1 := by rw [hτ]; exact hdown.1
  have hhit : ∀ᶠ x in 𝓝 y, projectiveOriginalFlow x 0 (τ x) 2 = 1 :=
    hnear.mono fun _ h => h.1.1.2.2
  have hcτ₁ : ContDiffAt ℝ 1 τ y := hcτ.of_le (by norm_num)
  have hformula := eventually_partialCore_multiplier_formula hk hD hcτ.continuousAt hpos
    (hnear.mono fun _ h => h.2) hcore hhit
  refine ⟨τ, hpos, hcτ, ?_, ?_, ?_⟩
  · filter_upwards [hnear, hformula] with x hx hf
    exact ⟨hx.1, hf⟩
  · intro i
    exact ⟨coreFlowMultiplier_pos _ _ _ _ i,
      contDiffAt_log_partialCoreReturnMultiplier hk hD hcτ₁ hpos.le hdom hA hcore i,
      contDiffAt_partialCoreReturnMultiplier hk hD hcτ₁ hpos.le hdom hA hcore i⟩
  · intro w dz Q₀
    have H := partialCoreReturn_log_derivative_bounds hk hD hcτ₁ hpos.le hdom hA hcore hhit hM w
      (fun t ht => hnorm t (hτ ▸ ht) w)
    constructor
    · exact H.1.trans_eq (by ring)
    · exact H.2.trans_eq (by ring)

end BianchiIX
