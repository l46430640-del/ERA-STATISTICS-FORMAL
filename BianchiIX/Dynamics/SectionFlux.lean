import BianchiIX.Dynamics.FlowTransport
import BianchiIX.Dynamics.CorrectedVolume
import BianchiIX.Analysis.VolumeForms

noncomputable section

namespace BianchiIX

open Set

def normalizedAmbientVolume : NormalizedState [⋀^Fin 5]→ₗ[ℝ] ℝ :=
  (Pi.basisFun ℝ (Fin 5)).det

/-- The radial normal is globally normalized by the quadratic constraint on its unit level. -/
def normalizedConstraintVolume (x : NormalizedState) (v : Fin 4 → NormalizedState) : ℝ :=
  normalizedAmbientVolume (Fin.cons ((1 / 2 : ℝ) • x) v) / normalizedVolumeWeight x

def normalizedSectionFlux (x : NormalizedState) (v : Fin 3 → NormalizedState) : ℝ :=
  normalizedConstraintVolume x (Fin.cons (normalizedField x) v)

theorem normalizedConstraintVolume_normal {x X : NormalizedState} {v : Fin 4 → NormalizedState}
    (hcon : stateConstraint x = 1) (hX : normalizedConstraintDifferential x X = 1)
    (hv : ∀ i, normalizedConstraintDifferential x (v i) = 0) :
    normalizedConstraintVolume x v =
      normalizedAmbientVolume (Fin.cons X v) / normalizedVolumeWeight x := by
  unfold normalizedConstraintVolume
  congr 1
  exact basis_det_cons_normal_independent (Pi.basisFun ℝ (Fin 5))
    hX (normalizedConstraintDifferential_normal hcon) hv

theorem normalizedConstraintVolume_flow {x : NormalizedState} {t₀ t : ℝ}
    (hpos : positiveWalls x) (hcon : stateConstraint x = 1)
    (ht : t ∈ normalizedMaxDomain x t₀) (v : Fin 4 → NormalizedState)
    (hv : ∀ i, normalizedConstraintDifferential x (v i) = 0) :
    normalizedConstraintVolume (normalizedMaxCurve x t₀ t)
        (fun i => normalizedFlowDifferential x t₀ t (v i)) =
      normalizedVolumeJacobian x t₀ t * normalizedConstraintVolume x v := by
  let z := normalizedMaxCurve x t₀ t
  let P := normalizedFlowDifferential x t₀ t
  have hp : positiveWalls z ∧ stateConstraint z = 1 :=
    (maximalNormalizedSolution x t₀).physical hpos hcon ht
  have hcov (u : NormalizedState) : normalizedConstraintDifferential z (P u) =
      normalizedConstraintDifferential x u :=
    congrArg (fun L : NormalizedState →L[ℝ] ℝ => L u) (normalizedConstraintDifferential_flow ht)
  have hnormal : normalizedConstraintDifferential z (P ((1 / 2 : ℝ) • x)) = 1 := by
    rw [hcov, normalizedConstraintDifferential_normal hcon]
  have hdet : normalizedAmbientVolume (Fin.cons (P ((1 / 2 : ℝ) • x)) (fun i => P (v i))) =
      P.det * normalizedAmbientVolume (Fin.cons ((1 / 2 : ℝ) • x) v) := by
    have H := (Pi.basisFun ℝ (Fin 5)).det_comp P.toLinearMap (Fin.cons ((1 / 2 : ℝ) • x) v)
    rw [Fin.comp_cons] at H
    exact H
  change normalizedConstraintVolume z (fun i => P (v i)) = _
  rw [normalizedConstraintVolume_normal hp.2 hnormal (fun i => (hcov (v i)).trans (hv i))]
  rw [hdet]
  have hw := ne_of_gt (normalizedVolumeWeight_pos hpos)
  unfold normalizedVolumeJacobian normalizedConstraintVolume
  dsimp [P, z]
  field_simp [hw]

theorem normalizedSectionFlux_flow {x : NormalizedState} {t₀ t : ℝ}
    (hpos : positiveWalls x) (hcon : stateConstraint x = 1)
    (ht : t ∈ normalizedMaxDomain x t₀) (v : Fin 3 → NormalizedState)
    (hv : ∀ i, normalizedConstraintDifferential x (v i) = 0) :
    normalizedSectionFlux (normalizedMaxCurve x t₀ t)
        (fun i => normalizedFlowDifferential x t₀ t (v i)) =
      normalizedVolumeJacobian x t₀ t * normalizedSectionFlux x v := by
  let w : Fin 4 → NormalizedState := Fin.cons (normalizedField x) v
  have htan : ∀ i : Fin 4, normalizedConstraintDifferential x (w i) = 0 := by
    intro i
    exact Fin.cases (normalizedConstraintDifferential_field x) hv i
  have H := normalizedConstraintVolume_flow hpos hcon ht w htan
  have heq : (fun i : Fin 4 => normalizedFlowDifferential x t₀ t (w i)) =
      Fin.cons (normalizedField (normalizedMaxCurve x t₀ t))
        (fun i => normalizedFlowDifferential x t₀ t (v i)) := by
    funext i
    exact Fin.cases (normalizedFlowDifferential_field ht) (fun _ => rfl) i
  rw [heq] at H
  exact H

theorem normalizedSectionFlux_add_flow (x X : NormalizedState)
    (v : Fin 3 → NormalizedState) (c : Fin 3 → ℝ) :
    normalizedAmbientVolume (Fin.cons X (Fin.cons (normalizedField x)
        (fun i => v i + c i • normalizedField x))) =
      normalizedAmbientVolume (Fin.cons X (Fin.cons (normalizedField x) v)) := by
  have hleft : Fin.cons X (Fin.cons (normalizedField x) (fun i => v i + c i • normalizedField x)) =
      ![X, normalizedField x, v 0 + c 0 • normalizedField x,
        v 1 + c 1 • normalizedField x, v 2 + c 2 • normalizedField x] := by
    ext i
    fin_cases i <;> rfl
  have hright : Fin.cons X (Fin.cons (normalizedField x) v) =
      ![X, normalizedField x, v 0, v 1, v 2] := by
    ext i
    fin_cases i <;> rfl
  rw [hleft, hright]
  exact alternating_fin5_add_flow normalizedAmbientVolume X (normalizedField x)
    (v 0) (v 1) (v 2) (c 0) (c 1) (c 2)

end BianchiIX
