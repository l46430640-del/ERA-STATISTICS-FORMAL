import BianchiIX.Dynamics.AxisMaps
import BianchiIX.Dynamics.SectionFlux

noncomputable section

namespace BianchiIX

open Set

/-- Linear changes of physical axes with their verified dynamical and volume identities. -/
structure NormalizedSymmetry where
  map : NormalizedState ≃L[ℝ] NormalizedState
  constraint : ∀ x, stateConstraint (map x) = stateConstraint x
  positive : ∀ x, positiveWalls (map x) ↔ positiveWalls x
  field : ∀ x, normalizedField (map x) = map (normalizedField x)
  weight : ∀ x, normalizedVolumeWeight (map x) = normalizedVolumeWeight x
  det : map.toLinearMap.det = 1

namespace NormalizedSymmetry

def refl : NormalizedSymmetry where
  map := ContinuousLinearEquiv.refl ℝ NormalizedState
  constraint _ := rfl
  positive _ := Iff.rfl
  field _ := rfl
  weight _ := rfl
  det := LinearMap.det_id

def trans (A B : NormalizedSymmetry) : NormalizedSymmetry where
  map := A.map.trans B.map
  constraint x := (B.constraint (A.map x)).trans (A.constraint x)
  positive x := (B.positive (A.map x)).trans (A.positive x)
  field x := by
    change normalizedField (B.map (A.map x)) = B.map (A.map (normalizedField x))
    rw [B.field, A.field]
  weight x := (B.weight (A.map x)).trans (A.weight x)
  det := by
    change (B.map.toLinearMap.comp A.map.toLinearMap).det = 1
    rw [LinearMap.det_comp, B.det, A.det, one_mul]

def symm (A : NormalizedSymmetry) : NormalizedSymmetry where
  map := A.map.symm
  constraint x := by simpa using (A.constraint (A.map.symm x)).symm
  positive x := by simpa using (A.positive (A.map.symm x)).symm
  field x := by
    apply A.map.injective
    rw [← A.field]
    simp
  weight x := by simpa using (A.weight (A.map.symm x)).symm
  det := by
    have H : A.map.toLinearMap.comp A.map.symm.toLinearMap = LinearMap.id := by
      ext x
      simp
    have hd := congrArg LinearMap.det H
    rw [LinearMap.det_comp, A.det, one_mul, LinearMap.det_id] at hd
    exact hd

def cycle : NormalizedSymmetry where
  map := axisCycleEquiv
  constraint := axisCycle_constraint
  positive := axisCycle_positive
  field := axisCycle_field
  weight x := by
    change normalizedVolumeWeight (axisCycle x) = normalizedVolumeWeight x
    simp only [normalizedVolumeWeight, wallAmplitude, axisCycle_wall_product]
  det := axisCycle_det

def swap : NormalizedSymmetry where
  map := axisSwapEquiv
  constraint := axisSwap_constraint
  positive := axisSwap_positive
  field := axisSwap_field
  weight x := by
    change normalizedVolumeWeight (axisSwap x) = normalizedVolumeWeight x
    simp only [normalizedVolumeWeight, wallAmplitude, axisSwap_wall_product]
  det := axisSwap_det

end NormalizedSymmetry

def NormalizedSolution.transform {x : NormalizedState} {t₀ : ℝ}
    (S : NormalizedSolution x t₀) (A : NormalizedSymmetry) : NormalizedSolution (A.map x) t₀ where
  domain := S.domain
  isOpen_domain := S.isOpen_domain
  convex_domain := S.convex_domain
  initial_mem := S.initial_mem
  curve := fun t => A.map (S.curve t)
  initial_eq := by rw [S.initial_eq]
  hasDerivAt t ht := by
    have H := A.map.hasFDerivAt.comp_hasDerivAt t (S.hasDerivAt t ht)
    rw [A.field]
    convert! H using 1

namespace NormalizedSymmetry

variable (A : NormalizedSymmetry)

theorem maxDomain (x : NormalizedState) (t₀ : ℝ) :
    normalizedMaxDomain (A.map x) t₀ = normalizedMaxDomain x t₀ := by
  apply Subset.antisymm
  · intro t ht
    have H := ((maximalNormalizedSolution (A.map x) t₀).transform A.symm).domain_subset_maximal ht
    simpa only [symm, ContinuousLinearEquiv.symm_apply_apply] using H
  · exact ((maximalNormalizedSolution x t₀).transform A).domain_subset_maximal

theorem maxCurve {x : NormalizedState} {t₀ t : ℝ} (ht : t ∈ normalizedMaxDomain x t₀) :
    normalizedMaxCurve (A.map x) t₀ t = A.map (normalizedMaxCurve x t₀ t) :=
  normalizedMaxCurve_eqOn ((maximalNormalizedSolution x t₀).transform A) ht

theorem ambientVolume (v : Fin 5 → NormalizedState) :
    normalizedAmbientVolume (fun i => A.map (v i)) = normalizedAmbientVolume v := by
  have H := (Pi.basisFun ℝ (Fin 5)).det_comp A.map.toLinearMap v
  rw [A.det, one_mul] at H
  convert! H using 1

theorem constraintVolume (x : NormalizedState) (v : Fin 4 → NormalizedState) :
    normalizedConstraintVolume (A.map x) (fun i => A.map (v i)) = normalizedConstraintVolume x v := by
  unfold normalizedConstraintVolume
  rw [← map_smul, A.weight]
  have H := A.ambientVolume (Fin.cons ((1 / 2 : ℝ) • x) v)
  change normalizedAmbientVolume (A.map ∘ Fin.cons ((1 / 2 : ℝ) • x) v) = _ at H
  rw [Fin.comp_cons] at H
  exact congrArg (fun z => z / normalizedVolumeWeight x) H

theorem sectionFlux (x : NormalizedState) (v : Fin 3 → NormalizedState) :
    normalizedSectionFlux (A.map x) (fun i => A.map (v i)) = normalizedSectionFlux x v := by
  unfold normalizedSectionFlux
  rw [A.field]
  have H := A.constraintVolume x (Fin.cons (normalizedField x) v)
  change normalizedConstraintVolume (A.map x) (A.map ∘ Fin.cons (normalizedField x) v) = _ at H
  rw [Fin.comp_cons] at H
  exact H

end NormalizedSymmetry

end BianchiIX
