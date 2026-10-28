import BianchiIX.Dynamics.AxisCharts
import BianchiIX.Measure.AxisHitting

noncomputable section

namespace BianchiIX

open Set MeasureTheory

def axisFamilyChart {ι : Type*} (B : ι → NormalizedSymmetry) (k : ι → ℝ)
    (z : ι × SectionCoordinates) : NormalizedState := axisWallChart (B z.1) (k z.1) z.2

def axisFamilySection {ι : Type*} (E : ι → Set SectionCoordinates) : Set (ι × SectionCoordinates) :=
  {z | z.2 ∈ E z.1}

theorem measurableSet_axisFamilySection {ι : Type*} [Countable ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] {E : ι → Set SectionCoordinates}
    (hE : ∀ i, MeasurableSet (E i)) : MeasurableSet (axisFamilySection E) := by
  have heq : axisFamilySection E = ⋃ i, ({i} ×ˢ E i) := by
    ext z
    simp [axisFamilySection]
  rw [heq]
  exact MeasurableSet.iUnion (fun i => (measurableSet_singleton i).prod (hE i))

def dominantWallChartDomain (h : ℝ) : Set SectionCoordinates :=
  {y | y ∈ mainWallChartDomain h ∧ Real.exp (-y 1) < h ∧ Real.exp (-y 2) < h}

theorem isOpen_dominantWallChartDomain (h : ℝ) : IsOpen (dominantWallChartDomain h) :=
  (isOpen_mainWallChartDomain h).inter
    ((isOpen_lt (show Continuous (fun y : SectionCoordinates => Real.exp (-y 1)) by fun_prop)
      continuous_const).inter
      (isOpen_lt (show Continuous (fun y : SectionCoordinates => Real.exp (-y 2)) by fun_prop)
        continuous_const))

theorem axisPermutationChart_walls (σ : Equiv.Perm (Fin 3)) (h : ℝ) (y : SectionCoordinates) (j : Fin 3) :
    normalizedWalls (axisWallChart (axisPermutation σ) h y) (σ j) =
      ![h, Real.exp (-y 1), Real.exp (-y 2)] j := by
  have H := congrArg (fun v : Fin 3 → ℝ => v j)
    (axisPermutation_walls σ (axisWallChart (axisPermutation σ) h y))
  simp only [axisWallChart, ContinuousLinearEquiv.apply_symm_apply] at H
  have H' : normalizedWalls (axisWallChart (axisPermutation σ) h y) (σ j) =
      normalizedWalls (mainWallChart h y) j := by convert! H.symm using 1
  rw [H']
  fin_cases j <;> rfl

theorem axisPermutationChart_other_wall_lt (σ : Equiv.Perm (Fin 3)) {h : ℝ} {y : SectionCoordinates}
    (hy : y ∈ dominantWallChartDomain h) {j : Fin 3} (hj : j ≠ σ 0) :
    normalizedWalls (axisWallChart (axisPermutation σ) h y) j < h := by
  obtain ⟨l, rfl⟩ := σ.surjective j
  rw [axisPermutationChart_walls]
  fin_cases l
  · exact (hj rfl).elim
  · exact hy.2.1
  · exact hy.2.2

/-- Distinct dominant walls give disjoint physical sections at a common wall height. -/
theorem axisPermutationFamilyChart_injOn {ι : Type*} (σ : ι → Equiv.Perm (Fin 3)) {h : ℝ}
    {E : ι → Set SectionCoordinates} (hσ : Function.Injective (fun i => σ i 0))
    (hE : ∀ i, E i ⊆ dominantWallChartDomain h) :
    InjOn (axisFamilyChart (fun i => axisPermutation (σ i)) (fun _ => h)) (axisFamilySection E) := by
  rintro ⟨i, x⟩ hx ⟨j, y⟩ hy heq
  have hij : i = j := by
    apply hσ
    by_contra hne
    have H := axisPermutationChart_other_wall_lt (σ j) (hE j hy) hne
    change axisWallChart (axisPermutation (σ i)) h x = axisWallChart (axisPermutation (σ j)) h y at heq
    rw [← heq, axisPermutationChart_walls] at H
    exact (lt_irrefl h) H
  subst j
  have hxy : x = y := axisWallChart_injective (axisPermutation (σ i)) h heq
  exact Prod.ext rfl hxy

/-- One verified frame for each possible dominant physical axis. -/
def primaryAxisFrame (i : Fin 3) : NormalizedSymmetry := axisPermutation (Equiv.swap 0 i)

theorem primaryAxisChart_injOn {h : ℝ} {E : Fin 3 → Set SectionCoordinates}
    (hE : ∀ i, E i ⊆ dominantWallChartDomain h) :
    InjOn (axisFamilyChart primaryAxisFrame (fun _ => h)) (axisFamilySection E) := by
  apply axisPermutationFamilyChart_injOn (fun i => Equiv.swap 0 i) _ hE
  intro i j hij
  simpa only [Equiv.swap_apply_left] using hij

theorem mem_dominantWallChartDomain_of_small {h : ℝ} {y : SectionCoordinates}
    (hh : 0 < h) (hy : y ∈ mainWallChartDomain h)
    (hb : Real.exp (-y 1) ≤ h / 8) (hc : Real.exp (-y 2) ≤ h / 8) :
    y ∈ dominantWallChartDomain h := by
  exact ⟨hy, lt_of_le_of_lt hb (by linarith), lt_of_le_of_lt hc (by linarith)⟩

theorem axisWallArrivalRelation_chart (A B : NormalizedSymmetry) {h k t₀ t : ℝ} {y : SectionCoordinates}
    (hh : 0 < h) (hy : (y, t) ∈ axisWallArrivalRelation A B h k t₀) :
    axisWallChart B k (axisWallCoordinates B (normalizedMaxCurve (axisWallChart A h y) t₀ t)) =
      normalizedMaxCurve (axisWallChart A h y) t₀ t := by
  have hp := (maximalNormalizedSolution (axisWallChart A h y) t₀).physical
    (axisWallChart_positive A hh y) (axisWallChart_constraint A hy.1) hy.2.1
  convert! (axisWallChart_coordinates B hp.1 hp.2 hy.2.2.2 hy.2.2.1).2 using 1

theorem axisFamilyHittingTimes_source {ι : Type*} {A : NormalizedSymmetry} {B : ι → NormalizedSymmetry}
    {h t₀ t : ℝ} {k : ι → ℝ} {E : ι → Set SectionCoordinates} {I : Set ℝ} {y : SectionCoordinates}
    (ht : t ∈ axisFamilyHittingTimes A B h k t₀ E I y) : y ∈ mainWallChartDomain h := by
  obtain ⟨_, _, hrel, _⟩ := ht
  exact hrel.1

end BianchiIX
