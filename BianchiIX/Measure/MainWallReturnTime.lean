import BianchiIX.Measure.MainWallReturnInjectivity

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal

namespace MainWallArrivalAtlas

variable {h k t₀ : ℝ} (C : MainWallArrivalAtlas h k t₀)

def firstTime (B : Set SectionCoordinates) (I : Set ℝ) (y : SectionCoordinates) : ℝ :=
  t₀ + (C.firstDelay B I y).toReal

theorem measurable_firstTime {B : Set SectionCoordinates} {I : Set ℝ}
    (hB : MeasurableSet B) (hI : MeasurableSet I) : Measurable (C.firstTime B I) :=
  measurable_const.add (C.measurable_firstDelay hB hI).ennreal_toReal

theorem firstTime_of_isLeast {B : Set SectionCoordinates} {I : Set ℝ} {y : SectionCoordinates}
    {t : ℝ} (hI : I ⊆ Ici t₀) (ht : IsLeast (mainWallHittingTimes h k t₀ B I y) t) :
    C.firstTime B I y = t := by
  rw [firstTime, (C.firstDelay_of_isLeast ht).1,
    ENNReal.toReal_ofReal (sub_nonneg.mpr (hI ht.1.1))]
  ring

end MainWallArrivalAtlas

/-- The real-valued extension is used only on the actual return domain. -/
theorem exists_measurable_mainWall_returnTime {h t₀ ε : ℝ} {B : Set SectionCoordinates}
    (hh : 0 < h) (hε : 0 < ε) (hbound : ∀ z ∈ B, mainWallChart h z 0 ≤ -ε)
    (hB : MeasurableSet B) :
    ∃ τ : SectionCoordinates → ℝ, Measurable τ ∧
      ∀ y ∈ mainWallReturnDomain h t₀ B,
        IsLeast (mainWallHittingTimes h h t₀ B (Ioi t₀) y) (τ y) := by
  obtain ⟨C⟩ := exists_mainWallArrivalAtlas (t₀ := t₀) hh hh
  have hI : Ioi t₀ ⊆ Ici t₀ := fun x hx => show t₀ ≤ x from le_of_lt hx
  refine ⟨C.firstTime B (Ioi t₀), C.measurable_firstTime hB measurableSet_Ioi, fun y hy => ?_⟩
  obtain ⟨t, ht⟩ := exists_mainWall_first_time hh hh hε hI hbound hy.2
  rwa [C.firstTime_of_isLeast hI ht]

theorem mainWall_firstReturn_eq_at_returnTime {h t₀ : ℝ} {B : Set SectionCoordinates}
    {R : SectionCoordinates → SectionCoordinates} {τ : SectionCoordinates → ℝ}
    (hfirst : ∀ y ∈ mainWallReturnDomain h t₀ B, ∃ t,
      IsLeast (mainWallHittingTimes h h t₀ B (Ioi t₀) y) t ∧
      R y = mainWallCoordinates (normalizedMaxCurve (mainWallChart h y) t₀ t))
    (hτ : ∀ y ∈ mainWallReturnDomain h t₀ B,
      IsLeast (mainWallHittingTimes h h t₀ B (Ioi t₀) y) (τ y))
    {y : SectionCoordinates} (hy : y ∈ mainWallReturnDomain h t₀ B) :
    R y = mainWallCoordinates (normalizedMaxCurve (mainWallChart h y) t₀ (τ y)) := by
  obtain ⟨t, ht, heq⟩ := hfirst y hy
  rwa [ht.unique (hτ y hy)] at heq

def cumulativeReturnTime {X : Type*} (R : X → X) (τ : X → ℝ) (t₀ : ℝ) (n : ℕ) (y : X) : ℝ :=
  t₀ + ∑ i ∈ Finset.range n, (τ (R^[i] y) - t₀)

@[simp] theorem cumulativeReturnTime_zero {X : Type*} (R : X → X) (τ : X → ℝ) (t₀ : ℝ) (y : X) :
    cumulativeReturnTime R τ t₀ 0 y = t₀ := by simp [cumulativeReturnTime]

theorem cumulativeReturnTime_succ {X : Type*} (R : X → X) (τ : X → ℝ) (t₀ : ℝ) (n : ℕ) (y : X) :
    cumulativeReturnTime R τ t₀ (n + 1) y = cumulativeReturnTime R τ t₀ n y + τ (R^[n] y) - t₀ := by
  simp only [cumulativeReturnTime, Finset.sum_range_succ]
  ring

theorem measurable_cumulativeReturnTime {X : Type*} [MeasurableSpace X]
    {R : X → X} {τ : X → ℝ} (hR : Measurable R) (hτ : Measurable τ) (t₀ : ℝ) (n : ℕ) :
    Measurable (cumulativeReturnTime R τ t₀ n) := by
  unfold cumulativeReturnTime
  exact measurable_const.add (Finset.measurable_sum _ (fun i _ => ((hτ.comp (hR.iterate i)).sub_const t₀)))

end BianchiIX
