import BianchiIX.Measure.GlobalWallHitting
import BianchiIX.Measure.MainWallFirstTime

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal

/-- The existing definition equals the initial state outside the maximal flow domain. -/
theorem measurable_normalizedMaxCurve (t₀ : ℝ) :
    Measurable (fun p : NormalizedState × ℝ => normalizedMaxCurve p.1 t₀ p.2) := by
  classical
  have H := ContinuousOn.measurable_piecewise
    (s := normalizedFlowDomain t₀)
    (f := fun p : NormalizedState × ℝ => normalizedMaxCurve p.1 t₀ p.2)
    (fun p hp => (normalizedMaxCurve_regular hp).2.continuousAt.continuousWithinAt)
    continuous_fst.continuousOn (isOpen_normalizedFlowDomain t₀).measurableSet
  convert! H using 1
  funext p
  by_cases hp : p ∈ normalizedFlowDomain t₀
  · simp only [piecewise_eq_of_mem _ _ _ hp]
  · rw [piecewise_eq_of_notMem _ _ _ hp]
    exact dif_neg hp

def globalAxisWallFirstTime {ι : Type*} (A : ι → NormalizedSymmetry) (h : ι → ℝ)
    (B : ι → Set SectionCoordinates) (I : Set ℝ) (x : NormalizedState) : ℝ :=
  (globalAxisWallFirstDelay A h B I x).toReal

def globalAxisWallFirstState {ι : Type*} (A : ι → NormalizedSymmetry) (h : ι → ℝ)
    (B : ι → Set SectionCoordinates) (I : Set ℝ) (x : NormalizedState) : NormalizedState :=
  normalizedMaxCurve x 0 (globalAxisWallFirstTime A h B I x)

theorem measurable_globalAxisWallFirstTime {ι : Type*} [Countable ι]
    (A : ι → NormalizedSymmetry) {h : ι → ℝ} {B : ι → Set SectionCoordinates} {I : Set ℝ}
    (hh : ∀ i, 0 < h i) (hB : ∀ i, MeasurableSet (B i)) (hI : MeasurableSet I)
    (hchart : ∀ i, B i ⊆ mainWallChartDomain (h i)) :
    Measurable (globalAxisWallFirstTime A h B I) :=
  (measurable_globalAxisWallFirstDelay A hh hB hI hchart).ennreal_toReal

theorem measurable_globalAxisWallFirstState {ι : Type*} [Countable ι]
    (A : ι → NormalizedSymmetry) {h : ι → ℝ} {B : ι → Set SectionCoordinates} {I : Set ℝ}
    (hh : ∀ i, 0 < h i) (hB : ∀ i, MeasurableSet (B i)) (hI : MeasurableSet I)
    (hchart : ∀ i, B i ⊆ mainWallChartDomain (h i)) :
    Measurable (globalAxisWallFirstState A h B I) :=
  (measurable_normalizedMaxCurve 0).comp
    (measurable_id.prodMk (measurable_globalAxisWallFirstTime A hh hB hI hchart))

theorem globalAxisWallFirstTime_of_isLeast {ι : Type*} (A : ι → NormalizedSymmetry)
    {h : ι → ℝ} {B : ι → Set SectionCoordinates} {I : Set ℝ} {x : NormalizedState} {t : ℝ}
    (hI : I ⊆ Ici 0) (ht : IsLeast (globalAxisWallHittingTimes A h B I x) t) :
    globalAxisWallFirstTime A h B I x = t := by
  rw [globalAxisWallFirstTime, globalAxisWallFirstDelay_of_isLeast A ht,
    ENNReal.toReal_ofReal (hI ht.1.1)]

/-- A Borel target need not be closed: the uniform shear margin prevents finite-time accumulation. -/
theorem globalAxisWallFirstTime_isLeast {ι : Type*} [Finite ι]
    (A : ι → NormalizedSymmetry) {h ε : ι → ℝ} {B : ι → Set SectionCoordinates} {I : Set ℝ}
    {x : NormalizedState} (hh : ∀ i, 0 < h i) (hε : ∀ i, 0 < ε i)
    (hp : positiveWalls x) (hc : stateConstraint x = 1) (hI : I ⊆ Ici 0)
    (hbound : ∀ i, ∀ y ∈ B i, mainWallChart (h i) y 0 ≤ -ε i)
    (hx : x ∈ globalAxisWallHittingDomain A h B I) :
    IsLeast (globalAxisWallHittingTimes A h B I x) (globalAxisWallFirstTime A h B I x) := by
  obtain ⟨t, ht⟩ := exists_globalAxisWall_first_time A hh hε hp hc hI hbound hx
  rwa [globalAxisWallFirstTime_of_isLeast A hI ht]

theorem globalAxisWallFirstState_mem {ι : Type*} [Finite ι]
    (A : ι → NormalizedSymmetry) {h ε : ι → ℝ} {B : ι → Set SectionCoordinates} {I : Set ℝ}
    {x : NormalizedState} (hh : ∀ i, 0 < h i) (hε : ∀ i, 0 < ε i)
    (hp : positiveWalls x) (hc : stateConstraint x = 1) (hI : I ⊆ Ici 0)
    (hbound : ∀ i, ∀ y ∈ B i, mainWallChart (h i) y 0 ≤ -ε i)
    (hx : x ∈ globalAxisWallHittingDomain A h B I) :
    ∃ i, ∃ y ∈ B i, axisWallChart (A i) (h i) y = globalAxisWallFirstState A h B I x :=
  (globalAxisWallFirstTime_isLeast A hh hε hp hc hI hbound hx).1.2.2

theorem globalAxisWallFirstTime_nonneg {ι : Type*} (A : ι → NormalizedSymmetry)
    (h : ι → ℝ) (B : ι → Set SectionCoordinates) (I : Set ℝ) (x : NormalizedState) :
    0 ≤ globalAxisWallFirstTime A h B I x := ENNReal.toReal_nonneg

theorem globalAxisWallFirstTime_of_not_mem {ι : Type*} (A : ι → NormalizedSymmetry)
    {h : ι → ℝ} {B : ι → Set SectionCoordinates} {I : Set ℝ} {x : NormalizedState}
    (hx : x ∉ globalAxisWallHittingDomain A h B I) : globalAxisWallFirstTime A h B I x = 0 := by
  have H : globalAxisWallFirstDelay A h B I x = ⊤ :=
    top_le_iff.mp (not_lt.mp (mt (globalAxisWallFirstDelay_lt_top_iff A h B I x).mp hx))
  simp [globalAxisWallFirstTime, H]

theorem globalAxisWallFirstState_of_not_mem {ι : Type*} (A : ι → NormalizedSymmetry)
    {h : ι → ℝ} {B : ι → Set SectionCoordinates} {I : Set ℝ} {x : NormalizedState}
    (hx : x ∉ globalAxisWallHittingDomain A h B I) : globalAxisWallFirstState A h B I x = x := by
  rw [globalAxisWallFirstState, globalAxisWallFirstTime_of_not_mem A hx, normalizedMaxCurve_initial]

theorem globalAxisWallFirstTime_small_target {ι : Type*} [Finite ι]
    (A : ι → NormalizedSymmetry) {h : ι → ℝ} {B : ι → Set SectionCoordinates} {I : Set ℝ}
    {x : NormalizedState} (hh : ∀ i, 0 < h i) (hh1 : ∀ i, h i ≤ 1 / 8)
    (hp : positiveWalls x) (hc : stateConstraint x = 1) (hI : I ⊆ Ici 0)
    (hsmall : ∀ i, ∀ y ∈ B i, y ∈ mainWallChartDomain (h i) ∧ |y 0| ≤ 1 / 8 ∧
      Real.exp (-y 1) ≤ h i / 8 ∧ Real.exp (-y 2) ≤ h i / 8)
    (hx : x ∈ globalAxisWallHittingDomain A h B I) :
    IsLeast (globalAxisWallHittingTimes A h B I x) (globalAxisWallFirstTime A h B I x) := by
  apply globalAxisWallFirstTime_isLeast A hh (ε := fun _ => 15 / 16)
    (fun _ => by norm_num) hp hc hI _ hx
  intro i y hy
  exact mainWall_small_target_shear (hh i) (hh1 i) (hsmall i y hy).1
    (hsmall i y hy).2.1 (hsmall i y hy).2.2.1 (hsmall i y hy).2.2.2

end BianchiIX
