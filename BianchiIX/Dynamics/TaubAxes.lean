import BianchiIX.Dynamics.TaubDistance
import BianchiIX.Dynamics.AxisFamilySections

noncomputable section

namespace BianchiIX

theorem normalizedState_eq_of_shears_walls {x y : NormalizedState}
    (hs : normalizedShears x = normalizedShears y) (hw : normalizedWalls x = normalizedWalls y) :
    x = y := by
  have hp := congrFun hs 0
  have hq := congrFun hs 1
  simp [normalizedShears] at hp hq
  have hp' : x 0 = y 0 := by linarith only [hp]
  have hq' : x 1 = y 1 := by
    have hn : Real.sqrt 3 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
    apply mul_left_cancel₀ hn
    linarith only [hp', hq]
  ext j
  fin_cases j
  · exact hp'
  · exact hq'
  · exact congrFun hw 0
  · exact congrFun hw 1
  · exact congrFun hw 2

theorem normalizedShears_taubPoint (i j : Fin 3) :
    normalizedShears (taubPoint i) j = if j = i then 2 else -1 := by
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  fin_cases i <;> fin_cases j <;> simp [taubPoint, normalizedShears] <;>
    nlinarith only [hs]

theorem normalizedWalls_taubPoint (i : Fin 3) : normalizedWalls (taubPoint i) = 0 := by
  fin_cases i <;> ext j <;> fin_cases j <;> rfl

theorem axisPermutation_taubPoint (σ : Equiv.Perm (Fin 3)) (i : Fin 3) :
    (axisPermutation σ).map (taubPoint i) = taubPoint (σ.symm i) := by
  apply normalizedState_eq_of_shears_walls
  · rw [axisPermutation_shears]
    ext j
    simp only [normalizedShears_taubPoint, Equiv.eq_symm_apply]
  · rw [axisPermutation_walls, normalizedWalls_taubPoint, normalizedWalls_taubPoint]
    rfl

theorem primaryAxisFrame_taubPoint (i : Fin 3) :
    (primaryAxisFrame i).map (taubPoint i) = taubPoint 0 := by
  simp [primaryAxisFrame, axisPermutation_taubPoint]

theorem axisPermutation_euclideanDistance (σ : Equiv.Perm (Fin 3)) (x y : NormalizedState) :
    normalizedEuclideanDistance ((axisPermutation σ).map x) ((axisPermutation σ).map y) =
      normalizedEuclideanDistance x y :=
  axisFrame_euclideanDistance _ x y

theorem axisPermutation_wallValue (σ : Equiv.Perm (Fin 3)) (x : NormalizedState) (i : Fin 3) :
    wallValue i ((axisPermutation σ).map x) = wallValue (σ i) x := by
  have heq (y : NormalizedState) (j : Fin 3) : normalizedWalls y j = wallValue j y := by
    fin_cases j <;> rfl
  simpa only [heq] using congrFun (axisPermutation_walls σ x) i

/-- A finite set of possible targets contains one target approached at arbitrary late times. -/
theorem exists_fixed_late_taub_target {α : ℝ → NormalizedState}
    (H : ∀ ε > (0 : ℝ), ∀ R : ℝ, ∃ t ≥ R, ∃ i : Fin 3,
      normalizedEuclideanDistance (α t) (taubPoint i) < ε) :
    ∃ i : Fin 3, ∀ ε > (0 : ℝ), ∀ R : ℝ, ∃ t ≥ R,
      normalizedEuclideanDistance (α t) (taubPoint i) < ε := by
  classical
  by_contra! hn
  choose ε hε R hR using hn
  obtain ⟨t, ht, i, hi⟩ := H (min (ε 0) (min (ε 1) (ε 2)))
    (lt_min (hε 0) (lt_min (hε 1) (hε 2))) (max (R 0) (max (R 1) (R 2)))
  have hti : R i ≤ t := by
    apply le_trans _ ht
    fin_cases i
    · exact le_max_left _ _
    · exact (le_max_left _ _).trans (le_max_right _ _)
    · exact (le_max_right _ _).trans (le_max_right _ _)
  have hei : min (ε 0) (min (ε 1) (ε 2)) ≤ ε i := by
    fin_cases i
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (min_le_left _ _)
    · exact (min_le_right _ _).trans (min_le_right _ _)
  exact (not_lt_of_ge (hR i t hti)) (hi.trans_le hei)

end BianchiIX
