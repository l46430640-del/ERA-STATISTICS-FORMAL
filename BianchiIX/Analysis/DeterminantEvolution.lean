import BianchiIX.Dynamics.WallEvolution
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Calculus.FDeriv.Analytic

noncomputable section

namespace BianchiIX

open Set MeasureTheory

private def determinantMultilinear {n : Type*} [Fintype n] [DecidableEq n] :
    ContinuousMultilinearMap ℝ (fun _ : n => n → ℝ) ℝ :=
  ⟨Matrix.detRowAlternating.toMultilinearMap, continuous_id.matrix_det⟩

/-- Row multilinearity gives Liouville's differential identity, even at singular matrices. -/
theorem hasDerivAt_matrix_det_of_mul {n : Type*} [Fintype n] [DecidableEq n]
    {A : ℝ → Matrix n n ℝ} {B : Matrix n n ℝ} {t : ℝ}
    (hA : HasDerivAt A (B * A t) t) :
    HasDerivAt (fun u => (A u).det) (B.trace * (A t).det) t := by
  have H := (determinantMultilinear.hasFDerivAt (A t)).comp_hasDerivAt t hA
  have hrow (i : n) : (B * A t) i = ∑ j, B i j • A t j := by
    ext j
    simp [Matrix.mul_apply]
  have hd : determinantMultilinear.linearDeriv (A t) (B * A t) = B.trace * (A t).det := by
    erw [ContinuousMultilinearMap.linearDeriv_apply]
    change (∑ i, (Matrix.updateRow (A t) i ((B * A t) i)).det) = _
    simp_rw [hrow, Matrix.det_updateRow_sum, smul_eq_mul]
    exact (Finset.sum_mul _ _ _).symm
  exact hd ▸ H

theorem matrix_det_eq_exp_integral {n : Type*} [Fintype n] [DecidableEq n]
    {I : Set ℝ} (hI : Convex ℝ I) (hopen : IsOpen I)
    {A B : ℝ → Matrix n n ℝ} (hc : ContinuousOn (fun u => (B u).trace) I)
    (hA : ∀ u ∈ I, HasDerivAt A (B u * A u) u)
    {t₀ t : ℝ} (ht₀ : t₀ ∈ I) (ht : t ∈ I) :
    (A t).det = (A t₀).det * Real.exp (∫ u in t₀..t, (B u).trace) :=
  homogeneous_solution_eq_exp_integral hI hopen hc
    (fun u hu => hasDerivAt_matrix_det_of_mul (hA u hu)) ht₀ ht

end BianchiIX
