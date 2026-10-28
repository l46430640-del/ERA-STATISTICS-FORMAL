import BianchiIX.Dynamics.OrbitSaturation
import BianchiIX.Dynamics.TaubAxes
import BianchiIX.Dynamics.TaubSubspace
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

noncomputable section

namespace BianchiIX

open Set Filter MeasureTheory
open scoped Topology

def physicalPhaseSpace : Set NormalizedState :=
  {x | positiveWalls x ∧ stateConstraint x = 1}

theorem measurableSet_physicalPhaseSpace : MeasurableSet physicalPhaseSpace :=
  isOpen_positiveWalls.measurableSet.inter
    (isClosed_eq (contDiff_stateConstraint 1).continuous continuous_const).measurableSet

theorem mem_physicalPhaseSpace_maxCurve_iff {x : NormalizedState} {t : ℝ}
    (ht : t ∈ normalizedMaxDomain x 0) :
    normalizedMaxCurve x 0 t ∈ physicalPhaseSpace ↔ x ∈ physicalPhaseSpace := by
  constructor
  · intro hx
    have H := (maximalNormalizedSolution (normalizedMaxCurve x 0 t) 0).physical
      hx.1 hx.2 (normalizedMaxCurve_inverse ht).1
    change normalizedMaxCurve (normalizedMaxCurve x 0 t) 0 (-t) ∈ physicalPhaseSpace at H
    rwa [(normalizedMaxCurve_inverse ht).2] at H
  · intro hx
    exact (maximalNormalizedSolution x 0).physical hx.1 hx.2 ht

theorem continuous_physical_forwardFlow {t : ℝ} (ht : 0 ≤ t) :
    Continuous (fun x : physicalPhaseSpace => normalizedMaxCurve x.val 0 t) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  have hF := (normalizedMaxCurve_regular
    (normalizedMaxDomain_contains_Ici_of_constraint x.property.2 0 ht)).2.continuousAt
  have hG : ContinuousAt (fun y : physicalPhaseSpace => (y.val, t)) x :=
    continuous_subtype_val.continuousAt.prodMk continuous_const.continuousAt
  have H := hF.comp (f := fun y : physicalPhaseSpace => (y.val, t)) hG
  exact H

def taubSubspaces : Set NormalizedState :=
  {x | ∃ i : Fin 3, normalizedTaubRadiusSq ((primaryAxisFrame i).map x) = 0}

theorem isClosed_taubSubspaces : IsClosed taubSubspaces := by
  have heq : taubSubspaces = ⋃ i : Fin 3,
      {x | normalizedTaubRadiusSq ((primaryAxisFrame i).map x) = 0} := by
    ext x; simp [taubSubspaces]
  rw [heq]
  apply isClosed_iUnion_of_finite
  intro i
  apply isClosed_eq _ continuous_const
  unfold normalizedTaubRadiusSq taubRadiusSq
  fun_prop

theorem mem_taubSubspaces_maxCurve_iff {x : NormalizedState} {t : ℝ}
    (ht : t ∈ normalizedMaxDomain x 0) :
    normalizedMaxCurve x 0 t ∈ taubSubspaces ↔ x ∈ taubSubspaces := by
  unfold taubSubspaces
  change (∃ i, normalizedTaubRadiusSq ((primaryAxisFrame i).map (normalizedMaxCurve x 0 t)) = 0) ↔ _
  apply exists_congr
  intro i
  have hdom : t ∈ normalizedMaxDomain ((primaryAxisFrame i).map x) 0 := by
    rwa [(primaryAxisFrame i).maxDomain]
  rw [← (primaryAxisFrame i).maxCurve ht, normalizedTaubRadiusSq_eq_zero_iff,
    normalizedTaubRadiusSq_eq_zero_iff]
  exact NormalizedSymmetry.swap.fixed_maxCurve_iff hdom

theorem not_mem_taubSubspaces_iff (x : NormalizedState) :
    x ∉ taubSubspaces ↔ ∀ i, 0 < normalizedTaubRadiusSq ((primaryAxisFrame i).map x) := by
  simp only [taubSubspaces, mem_ofPred_eq, not_exists]
  apply forall_congr'
  intro i
  constructor
  · intro h
    exact lt_of_le_of_ne (taubRadiusSq_nonneg _ _ _) (Ne.symm h)
  · exact ne_of_gt

end BianchiIX
