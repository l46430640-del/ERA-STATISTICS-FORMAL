import BianchiIX.Dynamics.Normalized
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Determinant

noncomputable section

namespace BianchiIX

/-- New axes `(1,2,3)` are old axes `(2,3,1)`. -/
def axisCycle (x : NormalizedState) : NormalizedState :=
  ![(-x 0 + Real.sqrt 3 * x 1) / 2, (-Real.sqrt 3 * x 0 - x 1) / 2, x 3, x 4, x 2]

/-- Exchange the second and third axes, including their shear components. -/
def axisSwap (x : NormalizedState) : NormalizedState := ![x 0, -x 1, x 2, x 4, x 3]

theorem axisCycle_twice (x : NormalizedState) :
    axisCycle (axisCycle x) =
      ![(-x 0 - Real.sqrt 3 * x 1) / 2, (Real.sqrt 3 * x 0 - x 1) / 2, x 4, x 2, x 3] := by
  have hs : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  ext i
  fin_cases i <;> dsimp [axisCycle] <;> ring_nf <;> norm_num [hs] <;> ring

theorem axisCycle_three (x : NormalizedState) : axisCycle (axisCycle (axisCycle x)) = x := by
  have hs : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  rw [axisCycle_twice]
  ext i
  fin_cases i <;> dsimp [axisCycle] <;> ring_nf <;> norm_num [hs] <;> ring

@[simp] theorem axisSwap_twice (x : NormalizedState) : axisSwap (axisSwap x) = x := by
  ext i
  fin_cases i <;> simp [axisSwap]

def axisCycleLinear : NormalizedState →ₗ[ℝ] NormalizedState where
  toFun := axisCycle
  map_add' x y := by
    ext i
    fin_cases i <;> simp [axisCycle] <;> ring
  map_smul' r x := by
    ext i
    fin_cases i <;> simp [axisCycle] <;> ring

def axisSwapLinear : NormalizedState →ₗ[ℝ] NormalizedState where
  toFun := axisSwap
  map_add' x y := by
    ext i
    fin_cases i <;> simp [axisSwap]
    ring
  map_smul' r x := by
    ext i
    fin_cases i <;> simp [axisSwap]

def axisCycleEquiv : NormalizedState ≃L[ℝ] NormalizedState :=
  ({ axisCycleLinear with
    invFun := fun x => axisCycle (axisCycle x)
    left_inv := axisCycle_three
    right_inv := axisCycle_three } : NormalizedState ≃ₗ[ℝ] NormalizedState).toContinuousLinearEquiv

def axisSwapEquiv : NormalizedState ≃L[ℝ] NormalizedState :=
  ({ axisSwapLinear with
    invFun := axisSwap
    left_inv := axisSwap_twice
    right_inv := axisSwap_twice } : NormalizedState ≃ₗ[ℝ] NormalizedState).toContinuousLinearEquiv

@[simp] theorem axisCycleEquiv_apply (x : NormalizedState) : axisCycleEquiv x = axisCycle x := rfl
@[simp] theorem axisSwapEquiv_apply (x : NormalizedState) : axisSwapEquiv x = axisSwap x := rfl

theorem axisCycle_constraint (x : NormalizedState) : stateConstraint (axisCycle x) = stateConstraint x := by
  have hs : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  dsimp [stateConstraint, constraint, shearSq, curvature, axisCycle]
  ring_nf
  norm_num [hs]
  ring

theorem axisSwap_constraint (x : NormalizedState) : stateConstraint (axisSwap x) = stateConstraint x := by
  dsimp [stateConstraint, constraint, shearSq, curvature, axisSwap]
  ring

theorem axisCycle_positive (x : NormalizedState) : positiveWalls (axisCycle x) ↔ positiveWalls x := by
  dsimp [positiveWalls, axisCycle]
  tauto

theorem axisSwap_positive (x : NormalizedState) : positiveWalls (axisSwap x) ↔ positiveWalls x := by
  dsimp [positiveWalls, axisSwap]
  tauto

theorem axisCycle_field (x : NormalizedState) : normalizedField (axisCycle x) = axisCycle (normalizedField x) := by
  have hs : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  ext i
  fin_cases i <;> dsimp [normalizedField, axisCycle, shearPlus, shearMinus,
    rateOne, rateTwo, rateThree, shearSq, curvature] <;> ring_nf <;> norm_num [hs] <;> ring

theorem axisSwap_field (x : NormalizedState) : normalizedField (axisSwap x) = axisSwap (normalizedField x) := by
  ext i
  fin_cases i <;> dsimp [normalizedField, axisSwap, shearPlus, shearMinus,
    rateOne, rateTwo, rateThree, shearSq, curvature] <;> ring

theorem axisCycle_wall_product (x : NormalizedState) :
    axisCycle x 2 * axisCycle x 3 * axisCycle x 4 = x 2 * x 3 * x 4 := by
  dsimp [axisCycle]
  ring

theorem axisSwap_wall_product (x : NormalizedState) :
    axisSwap x 2 * axisSwap x 3 * axisSwap x 4 = x 2 * x 3 * x 4 := by
  dsimp [axisSwap]
  ring

theorem axisCycle_det : axisCycleEquiv.toLinearMap.det = 1 := by
  have hs : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  rw [← LinearMap.det_toMatrix']
  have hm : LinearMap.toMatrix' axisCycleEquiv.toLinearMap =
      !![-1 / 2, Real.sqrt 3 / 2, 0, 0, 0; -Real.sqrt 3 / 2, -1 / 2, 0, 0, 0;
        0, 0, 0, 1, 0; 0, 0, 0, 0, 1; 0, 0, 1, 0, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [LinearMap.toMatrix'_apply, axisCycleEquiv, axisCycleLinear, axisCycle, Pi.single_apply, Fin.ext_iff]
  rw [hm]
  norm_num [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Matrix.det_fin_two,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail, hs]
  change (1 : ℝ) / 4 + -(Real.sqrt 3 / 2 * (-Real.sqrt 3 / 2 * 1)) = 1
  nlinarith [hs]

theorem axisSwap_det : axisSwapEquiv.toLinearMap.det = 1 := by
  rw [← LinearMap.det_toMatrix']
  have hm : LinearMap.toMatrix' axisSwapEquiv.toLinearMap =
      !![1, 0, 0, 0, 0; 0, -1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 0, 1; 0, 0, 0, 1, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [LinearMap.toMatrix'_apply, axisSwapEquiv, axisSwapLinear, axisSwap, Pi.single_apply, Fin.ext_iff]
  rw [hm]
  norm_num [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Matrix.det_fin_two,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail]

end BianchiIX
