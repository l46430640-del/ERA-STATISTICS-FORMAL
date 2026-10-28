import BianchiIX.Dynamics.AxisSymmetry

noncomputable section

namespace BianchiIX

def normalizedShears (x : NormalizedState) : Fin 3 → ℝ :=
  ![-2 * x 0, x 0 - Real.sqrt 3 * x 1, x 0 + Real.sqrt 3 * x 1]

def normalizedWalls (x : NormalizedState) : Fin 3 → ℝ := ![x 2, x 3, x 4]

theorem axisCycle_shears (x : NormalizedState) :
    normalizedShears (axisCycle x) = ![normalizedShears x 1, normalizedShears x 2, normalizedShears x 0] := by
  have hs : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  ext i
  fin_cases i <;> dsimp [normalizedShears, axisCycle] <;> ring_nf <;> norm_num [hs] <;> ring

theorem axisSwap_shears (x : NormalizedState) :
    normalizedShears (axisSwap x) = ![normalizedShears x 0, normalizedShears x 2, normalizedShears x 1] := by
  ext i
  fin_cases i <;> dsimp [normalizedShears, axisSwap] <;> ring

open NormalizedSymmetry in
def axisFrame (i : Fin 6) : NormalizedSymmetry :=
  ![refl, cycle, cycle.trans cycle, swap, cycle.trans swap, (cycle.trans cycle).trans swap] i

def axisOrder (i : Fin 6) : Fin 3 → Fin 3 :=
  ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1], ![0, 2, 1], ![1, 0, 2], ![2, 1, 0]] i

theorem axisOrder_bijective : ∀ i, Function.Bijective (axisOrder i) := by decide

theorem axisOrder_covers : ∀ σ : Equiv.Perm (Fin 3), ∃ i, ∀ j, axisOrder i j = σ j := by decide

theorem axisFrame_apply (i : Fin 6) (x : NormalizedState) :
    (axisFrame i).map x =
      ![x, axisCycle x, axisCycle (axisCycle x), axisSwap x,
        axisSwap (axisCycle x), axisSwap (axisCycle (axisCycle x))] i := by
  fin_cases i <;> rfl

theorem axisFrame_walls (i : Fin 6) (x : NormalizedState) :
    normalizedWalls ((axisFrame i).map x) = fun j => normalizedWalls x (axisOrder i j) := by
  rw [axisFrame_apply]
  fin_cases i <;> ext j <;> fin_cases j <;> rfl

theorem axisFrame_shears (i : Fin 6) (x : NormalizedState) :
    normalizedShears ((axisFrame i).map x) = fun j => normalizedShears x (axisOrder i j) := by
  rw [axisFrame_apply]
  fin_cases i
  · ext j
    fin_cases j <;> rfl
  · change normalizedShears (axisCycle x) = _
    rw [axisCycle_shears]
    ext j
    fin_cases j <;> rfl
  · change normalizedShears (axisCycle (axisCycle x)) = _
    simp only [axisCycle_shears]
    ext j
    fin_cases j <;> rfl
  · change normalizedShears (axisSwap x) = _
    rw [axisSwap_shears]
    ext j
    fin_cases j <;> rfl
  · change normalizedShears (axisSwap (axisCycle x)) = _
    simp only [axisSwap_shears, axisCycle_shears]
    ext j
    fin_cases j <;> rfl
  · change normalizedShears (axisSwap (axisCycle (axisCycle x))) = _
    simp only [axisSwap_shears, axisCycle_shears]
    ext j
    fin_cases j <;> rfl

/-- Each permutation acts on walls and diagonal shear by exactly the same permutation. -/
def axisPermutation (σ : Equiv.Perm (Fin 3)) : NormalizedSymmetry :=
  axisFrame (axisOrder_covers σ).choose

theorem axisPermutation_walls (σ : Equiv.Perm (Fin 3)) (x : NormalizedState) :
    normalizedWalls ((axisPermutation σ).map x) = fun j => normalizedWalls x (σ j) := by
  rw [axisPermutation, axisFrame_walls]
  funext j
  rw [(axisOrder_covers σ).choose_spec j]

theorem axisPermutation_shears (σ : Equiv.Perm (Fin 3)) (x : NormalizedState) :
    normalizedShears ((axisPermutation σ).map x) = fun j => normalizedShears x (σ j) := by
  rw [axisPermutation, axisFrame_shears]
  funext j
  rw [(axisOrder_covers σ).choose_spec j]

theorem axisPermutation_maxDomain (σ : Equiv.Perm (Fin 3)) (x : NormalizedState) (t₀ : ℝ) :
    normalizedMaxDomain ((axisPermutation σ).map x) t₀ = normalizedMaxDomain x t₀ :=
  (axisPermutation σ).maxDomain x t₀

theorem axisPermutation_maxCurve (σ : Equiv.Perm (Fin 3)) {x : NormalizedState} {t₀ t : ℝ}
    (ht : t ∈ normalizedMaxDomain x t₀) :
    normalizedMaxCurve ((axisPermutation σ).map x) t₀ t =
      (axisPermutation σ).map (normalizedMaxCurve x t₀ t) :=
  (axisPermutation σ).maxCurve ht

theorem axisPermutation_sectionFlux (σ : Equiv.Perm (Fin 3)) (x : NormalizedState)
    (v : Fin 3 → NormalizedState) :
    normalizedSectionFlux ((axisPermutation σ).map x) (fun i => (axisPermutation σ).map (v i)) =
      normalizedSectionFlux x v :=
  (axisPermutation σ).sectionFlux x v

end BianchiIX
