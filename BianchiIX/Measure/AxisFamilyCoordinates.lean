import BianchiIX.Dynamics.AxisFamilySections
import Mathlib.MeasureTheory.Constructions.Polish.Basic

noncomputable section

namespace BianchiIX

open Set MeasureTheory

theorem continuous_axisFamilyChart {ι : Type*} [TopologicalSpace ι] [DiscreteTopology ι]
    (A : ι → NormalizedSymmetry) (h : ι → ℝ) : Continuous (axisFamilyChart A h) := by
  apply continuous_prod_of_discrete_left.mpr
  intro i
  apply (A i).map.symm.continuous.comp
  change Continuous (mainWallChart (h i))
  unfold mainWallChart mainWallRadicand curvature
  fun_prop

/-- Inverting the disjoint physical sections recovers both the axis and its coordinates measurably. -/
theorem exists_measurable_primaryAxis_coordinates {h : ℝ} {E : Fin 3 → Set SectionCoordinates}
    (hE : ∀ i, MeasurableSet (E i))
    (hinj : InjOn (axisFamilyChart primaryAxisFrame (fun _ => h)) (axisFamilySection E)) :
    ∃ c : NormalizedState → Fin 3 × SectionCoordinates, Measurable c ∧
      ∀ z ∈ axisFamilySection E, c (axisFamilyChart primaryAxisFrame (fun _ => h) z) = z := by
  classical
  by_cases hne : (axisFamilySection E).Nonempty
  · let : Nonempty (axisFamilySection E) := hne.to_subtype
    have H := (continuous_axisFamilyChart primaryAxisFrame (fun _ => h)).continuousOn.measurableEmbedding
      (measurableSet_axisFamilySection hE) hinj
    refine ⟨fun x => (H.invFun x).val, measurable_subtype_coe.comp H.measurable_invFun, ?_⟩
    intro z hz
    exact congrArg Subtype.val (H.leftInverse_invFun ⟨z, hz⟩)
  · exact ⟨fun _ => (0, 0), measurable_const, fun z hz => (hne ⟨z, hz⟩).elim⟩

end BianchiIX
