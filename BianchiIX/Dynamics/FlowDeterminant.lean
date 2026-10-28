import BianchiIX.Dynamics.GlobalVariation
import BianchiIX.Analysis.DeterminantEvolution
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Analysis.Calculus.Deriv.Pi

noncomputable section

namespace BianchiIX

open Set MeasureTheory

def normalizedMatrix (A : NormalizedVariation) : Matrix (Fin 5) (Fin 5) ℝ :=
  LinearMap.toMatrix' A.toLinearMap

theorem normalizedMatrix_apply (A : NormalizedVariation) (i j : Fin 5) :
    normalizedMatrix A i j = A (Pi.single j 1) i := rfl

theorem normalizedMatrix_comp (A B : NormalizedVariation) :
    normalizedMatrix (A.comp B) = normalizedMatrix A * normalizedMatrix B :=
  LinearMap.toMatrix'_comp A.toLinearMap B.toLinearMap

theorem normalizedMatrix_det (A : NormalizedVariation) :
    (normalizedMatrix A).det = A.det := LinearMap.det_toMatrix' A.toLinearMap

theorem continuous_normalizedMatrix : Continuous normalizedMatrix := by
  change Continuous (fun A : NormalizedVariation => fun i j => A (Pi.single j 1) i)
  fun_prop

theorem hasDerivAt_normalizedMatrix {A : ℝ → NormalizedVariation} {B : NormalizedVariation}
    {t : ℝ} (hA : HasDerivAt A B t) :
    HasDerivAt (fun u => normalizedMatrix (A u)) (normalizedMatrix B) t := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  have H := hasDerivAt_pi.mp (hA.clm_apply (hasDerivAt_const t (Pi.single j (1 : ℝ)))) i
  simpa only [normalizedMatrix_apply, ContinuousLinearMap.map_zero, add_zero] using H

/-- Divergence in the ambient five original coordinates, before restricting the constraint. -/
def normalizedDivergence (x : NormalizedState) : ℝ :=
  2 * curvature (x 2) (x 3) (x 4) - 3 * shearSq (x 0) (x 1)

private theorem normalizedDifferential_diagonal (x : NormalizedState) (i : Fin 5) :
    normalizedDifferential x (Pi.single i 1) i =
      ![curvature (x 2) (x 3) (x 4), curvature (x 2) (x 3) (x 4),
        rateOne (x 0) (x 1), rateTwo (x 0) (x 1), rateThree (x 0) (x 1)] i := by
  have H := hasDerivAt_pi.mp
    ((hasFDerivAt_normalizedField (Function.update x i (x i))).comp_hasDerivAt (x i)
      (hasDerivAt_update x i (x i))) i
  simp only [Function.update_eq_self] at H
  apply H.unique
  fin_cases i
  · simpa [normalizedField, shearPlus] using
      (((((((hasDerivAt_id (x 0)).const_mul (curvature (x 2) (x 3) (x 4))).sub_const
        (2 * x 2 ^ 2)).add_const (x 3 ^ 2)).add_const (x 4 ^ 2)).add_const (x 2 * x 3)).sub_const
        (2 * x 3 * x 4)).add_const (x 2 * x 4)
  · simpa [normalizedField, shearMinus] using
      ((hasDerivAt_id (x 1)).const_mul (curvature (x 2) (x 3) (x 4))).add_const
        (Real.sqrt 3 * (-x 3 ^ 2 + x 4 ^ 2 + x 2 * x 3 - x 2 * x 4))
  · simpa [normalizedField] using (hasDerivAt_id (x 2)).const_mul (rateOne (x 0) (x 1))
  · simpa [normalizedField] using (hasDerivAt_id (x 3)).const_mul (rateTwo (x 0) (x 1))
  · simpa [normalizedField] using (hasDerivAt_id (x 4)).const_mul (rateThree (x 0) (x 1))

theorem trace_normalizedDifferential (x : NormalizedState) :
    (normalizedMatrix (normalizedDifferential x)).trace = normalizedDivergence x := by
  simp only [Matrix.trace, Matrix.diag, normalizedMatrix_apply, normalizedDifferential_diagonal]
  simp [Fin.sum_univ_succ, normalizedDivergence, rateOne, rateTwo, rateThree]
  ring

theorem hasDerivAt_normalizedFlowDeterminant {x : NormalizedState} {t₀ t : ℝ}
    (ht : t ∈ normalizedMaxDomain x t₀) :
    HasDerivAt (fun u => (normalizedFlowDifferential x t₀ u).det)
      (normalizedDivergence (normalizedMaxCurve x t₀ t) *
        (normalizedFlowDifferential x t₀ t).det) t := by
  have H := hasDerivAt_normalizedMatrix (hasDerivAt_normalizedFlowDifferential ht)
  rw [normalizedMatrix_comp] at H
  simpa only [normalizedMatrix_det, trace_normalizedDifferential] using
    hasDerivAt_matrix_det_of_mul H

theorem normalizedFlowDeterminant_eq_exp_integral {x : NormalizedState} {t₀ t : ℝ}
    (ht : t ∈ normalizedMaxDomain x t₀) :
    (normalizedFlowDifferential x t₀ t).det =
      Real.exp (∫ u in t₀..t, normalizedDivergence (normalizedMaxCurve x t₀ u)) := by
  have hc : Continuous normalizedDivergence := by
    unfold normalizedDivergence curvature shearSq
    fun_prop
  have H := homogeneous_solution_eq_exp_integral (convex_normalizedMaxDomain x t₀)
    (isOpen_normalizedMaxDomain x t₀)
    (hc.comp_continuousOn (HasDerivAt.continuousOn (fun _ hu => hasDerivAt_normalizedMaxCurve hu)))
    (fun _ hu => hasDerivAt_normalizedFlowDeterminant hu)
    (initial_mem_normalizedMaxDomain x t₀) ht
  simpa [normalizedFlowDifferential_initial, ContinuousLinearMap.det] using H

theorem normalizedFlowDeterminant_pos {x : NormalizedState} {t₀ t : ℝ}
    (ht : t ∈ normalizedMaxDomain x t₀) : 0 < (normalizedFlowDifferential x t₀ t).det := by
  rw [normalizedFlowDeterminant_eq_exp_integral ht]
  exact Real.exp_pos _

end BianchiIX
