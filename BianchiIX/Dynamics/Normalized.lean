import BianchiIX.Algebra.Flow
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp

noncomputable section

namespace BianchiIX

open Set

/-- Coordinates are `(p, s, N₁, N₂, N₃)`, with the finite-dimensional sup norm. -/
abbrev NormalizedState := Fin 5 → ℝ

def normalizedField (x : NormalizedState) : NormalizedState :=
  ![shearPlus (x 0) (x 2) (x 3) (x 4),
    shearMinus (x 1) (x 2) (x 3) (x 4),
    rateOne (x 0) (x 1) * x 2,
    rateTwo (x 0) (x 1) * x 3,
    rateThree (x 0) (x 1) * x 4]

def stateConstraint (x : NormalizedState) : ℝ := constraint (x 0) (x 1) (x 2) (x 3) (x 4)

def positiveWalls (x : NormalizedState) : Prop := 0 < x 2 ∧ 0 < x 3 ∧ 0 < x 4

theorem contDiff_normalizedField (n : WithTop ℕ∞) : ContDiff ℝ n normalizedField := by
  rw [contDiff_pi]
  intro i
  fin_cases i <;>
    dsimp [normalizedField, shearPlus, shearMinus, rateOne, rateTwo, rateThree, shearSq, curvature] <;>
    fun_prop

theorem contDiff_stateConstraint (n : WithTop ℕ∞) : ContDiff ℝ n stateConstraint := by
  unfold stateConstraint constraint shearSq curvature
  fun_prop

theorem isOpen_positiveWalls : IsOpen {x : NormalizedState | positiveWalls x} :=
  (isOpen_lt continuous_const (continuous_apply 2)).inter
    ((isOpen_lt continuous_const (continuous_apply 3)).inter
      (isOpen_lt continuous_const (continuous_apply 4)))

theorem hasDerivAt_normalized_components {α : ℝ → NormalizedState} {t : ℝ}
    (hα : HasDerivAt α (normalizedField (α t)) t) :
    HasDerivAt (fun u => α u 0) (shearPlus (α t 0) (α t 2) (α t 3) (α t 4)) t ∧
    HasDerivAt (fun u => α u 1) (shearMinus (α t 1) (α t 2) (α t 3) (α t 4)) t ∧
    HasDerivAt (fun u => α u 2) (rateOne (α t 0) (α t 1) * α t 2) t ∧
    HasDerivAt (fun u => α u 3) (rateTwo (α t 0) (α t 1) * α t 3) t ∧
    HasDerivAt (fun u => α u 4) (rateThree (α t 0) (α t 1) * α t 4) t :=
  ⟨hasDerivAt_pi.mp hα 0, hasDerivAt_pi.mp hα 1, hasDerivAt_pi.mp hα 2,
    hasDerivAt_pi.mp hα 3, hasDerivAt_pi.mp hα 4⟩

theorem hasDerivAt_stateConstraint {α : ℝ → NormalizedState} {t : ℝ}
    (hα : HasDerivAt α (normalizedField (α t)) t) :
    HasDerivAt (fun u => stateConstraint (α u)) 0 t := by
  obtain ⟨hp, hs, ha, hb, hc⟩ := hasDerivAt_normalized_components hα
  exact hasDerivAt_constraint hp hs ha hb hc

theorem normalized_constraint_constant {I : Set ℝ} (hI : Convex ℝ I)
    {α : ℝ → NormalizedState} (hα : ∀ t ∈ I, HasDerivAt α (normalizedField (α t)) t)
    {t₀ t : ℝ} (ht₀ : t₀ ∈ I) (ht : t ∈ I) :
    stateConstraint (α t) = stateConstraint (α t₀) := by
  have H := hI.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun u hu => (hasDerivAt_stateConstraint (hα u hu)).hasDerivWithinAt)
    (C := 0) (fun _ _ => by simp) ht₀ ht
  simpa only [zero_mul, norm_le_zero_iff, sub_eq_zero] using H

end BianchiIX
