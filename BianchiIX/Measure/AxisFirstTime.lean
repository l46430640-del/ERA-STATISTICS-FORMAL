import BianchiIX.Measure.AxisHitting
import BianchiIX.Dynamics.AxisSectionCrossings

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal

theorem finite_axisFamilyHittingTimes {ι : Type*} [Finite ι]
    (A : NormalizedSymmetry) (B : ι → NormalizedSymmetry) {h t₀ T : ℝ} {k ε : ι → ℝ}
    {E : ι → Set SectionCoordinates} {I : Set ℝ} {y : SectionCoordinates}
    (hh : 0 < h) (hk : ∀ i, 0 < k i) (hε : ∀ i, 0 < ε i)
    (hy : y ∈ mainWallChartDomain h)
    (hbound : ∀ i, ∀ z ∈ E i, mainWallChart (k i) z 0 ≤ -ε i) :
    (axisFamilyHittingTimes A B h k t₀ E I y ∩ Icc t₀ T).Finite := by
  have hpos := axisWallChart_positive A hh y
  have hcon := axisWallChart_constraint A hy
  apply (finite_axisSectionTimes_iUnion B hk hε hpos hcon).subset
  rintro t ⟨⟨_, i, hrel, hE⟩, htK⟩
  have hphys := (maximalNormalizedSolution (axisWallChart A h y) t₀).physical hpos hcon hrel.2.1
  have hc := axisWallChart_coordinates (B i) hphys.1 hphys.2 hrel.2.2.2 hrel.2.2.1
  have heq : mainWallChart (k i)
      (axisWallCoordinates (B i) (normalizedMaxCurve (axisWallChart A h y) t₀ t)) =
      (B i).map (normalizedMaxCurve (axisWallChart A h y) t₀ t) := by
    have H := congrArg (B i).map hc.2
    simp only [axisWallChart, ContinuousLinearEquiv.apply_symm_apply] at H
    convert! H using 1
  have H := hbound i _ hE
  rw [heq] at H
  exact mem_iUnion.mpr ⟨i, htK, hrel.2.2.1, H⟩

/-- Finite families admit a genuine first hit, even for nonclosed targets and allowed time sets. -/
theorem exists_axisFamily_first_time {ι : Type*} [Finite ι]
    (A : NormalizedSymmetry) (B : ι → NormalizedSymmetry) {h t₀ : ℝ} {k ε : ι → ℝ}
    {E : ι → Set SectionCoordinates} {I : Set ℝ} {y : SectionCoordinates}
    (hh : 0 < h) (hk : ∀ i, 0 < k i) (hε : ∀ i, 0 < ε i) (hI : I ⊆ Ici t₀)
    (hbound : ∀ i, ∀ z ∈ E i, mainWallChart (k i) z 0 ≤ -ε i)
    (hy : y ∈ axisFamilyHittingDomain A B h k t₀ E I) :
    ∃ t, IsLeast (axisFamilyHittingTimes A B h k t₀ E I y) t := by
  obtain ⟨b, hb⟩ := hy
  have hsource : y ∈ mainWallChartDomain h := by
    obtain ⟨i, hi, _⟩ := hb.2
    exact hi.1
  have hfinite := finite_axisFamilyHittingTimes A B (t₀ := t₀) (T := b) (I := I) hh hk hε hsource hbound
  obtain ⟨t, ht, hmin⟩ := Set.exists_min_image
    (axisFamilyHittingTimes A B h k t₀ E I y ∩ Icc t₀ b) id hfinite
      ⟨b, hb, hI hb.1, le_rfl⟩
  refine ⟨t, ht.1, fun u hu => ?_⟩
  by_cases hub : u ≤ b
  · exact hmin u ⟨hu, hI hu.1, hub⟩
  · exact ht.2.2.trans (le_of_not_ge hub)

namespace AxisWallAtlasFamily

variable {ι : Type*} {A : NormalizedSymmetry} {B : ι → NormalizedSymmetry}
  {h t₀ : ℝ} {k : ι → ℝ} (C : AxisWallAtlasFamily A B h k t₀)

theorem firstDelay_of_isLeast {E : ι → Set SectionCoordinates} {I : Set ℝ} {y : SectionCoordinates}
    {t : ℝ} (ht : IsLeast (axisFamilyHittingTimes A B h k t₀ E I y) t) :
    C.firstDelay E I y = ENNReal.ofReal (t - t₀) ∧
      ∃ i n, y ∈ ((C i).branch n).eligible (E i) I ∧ ((C i).branch n).coordinateTime y = t := by
  classical
  obtain ⟨i, hrel, hE⟩ := ht.1.2
  obtain ⟨n, hyn, hn⟩ := ((C i).mem_relation_iff y t).mp hrel
  have heligible : y ∈ ((C i).branch n).eligible (E i) I := by
    refine ⟨hyn, ?_, ?_⟩
    · rw [hn]
      exact ht.1.1
    · rwa [((C i).branch n).map_eq_coordinates hyn, hn]
  refine ⟨le_antisymm ?_ ?_, i, n, heligible, hn⟩
  · calc
      C.firstDelay E I y ≤ ((C i).branch n).delay (E i) I y := iInf_le_of_le i (iInf_le _ n)
      _ = ENNReal.ofReal (t - t₀) := by rw [((C i).branch n).delay_of_mem heligible, hn]
  · apply le_iInf
    intro j
    apply le_iInf
    intro m
    by_cases hym : y ∈ ((C j).branch m).eligible (E j) I
    · rw [((C j).branch m).delay_of_mem hym]
      apply ENNReal.ofReal_le_ofReal
      apply sub_le_sub_right
      apply ht.2
      refine ⟨hym.2.1, j, ((C j).branch m).mem_relation hym.1, ?_⟩
      rw [← ((C j).branch m).map_eq_coordinates hym.1]
      exact hym.2.2
    · simp [AxisWallArrival.delay, hym]

theorem exists_firstDelay_branch [Finite ι] {ε : ι → ℝ}
    {E : ι → Set SectionCoordinates} {I : Set ℝ} {y : SectionCoordinates}
    (hh : 0 < h) (hk : ∀ i, 0 < k i) (hε : ∀ i, 0 < ε i) (hI : I ⊆ Ici t₀)
    (hbound : ∀ i, ∀ z ∈ E i, mainWallChart (k i) z 0 ≤ -ε i)
    (hy : y ∈ axisFamilyHittingDomain A B h k t₀ E I) :
    ∃ i n, y ∈ ((C i).branch n).eligible (E i) I ∧
      ((C i).branch n).delay (E i) I y = C.firstDelay E I y ∧
      IsLeast (axisFamilyHittingTimes A B h k t₀ E I y) (((C i).branch n).coordinateTime y) := by
  obtain ⟨t, ht⟩ := exists_axisFamily_first_time A B hh hk hε hI hbound hy
  obtain ⟨hfirst, i, n, hyn, hn⟩ := C.firstDelay_of_isLeast ht
  refine ⟨i, n, hyn, ?_, ?_⟩
  · rw [((C i).branch n).delay_of_mem hyn, hn, hfirst]
  · rwa [hn]

def firstTime (E : ι → Set SectionCoordinates) (I : Set ℝ) (y : SectionCoordinates) : ℝ :=
  t₀ + (C.firstDelay E I y).toReal

theorem measurable_firstTime [Countable ι] {E : ι → Set SectionCoordinates} {I : Set ℝ}
    (hE : ∀ i, MeasurableSet (E i)) (hI : MeasurableSet I) : Measurable (C.firstTime E I) :=
  measurable_const.add (C.measurable_firstDelay hE hI).ennreal_toReal

theorem firstTime_of_isLeast {E : ι → Set SectionCoordinates} {I : Set ℝ} {y : SectionCoordinates}
    {t : ℝ} (hI : I ⊆ Ici t₀) (ht : IsLeast (axisFamilyHittingTimes A B h k t₀ E I y) t) :
    C.firstTime E I y = t := by
  rw [firstTime, (C.firstDelay_of_isLeast ht).1,
    ENNReal.toReal_ofReal (sub_nonneg.mpr (hI ht.1.1))]
  ring

theorem firstTime_isLeast [Finite ι] {ε : ι → ℝ}
    {E : ι → Set SectionCoordinates} {I : Set ℝ} {y : SectionCoordinates}
    (hh : 0 < h) (hk : ∀ i, 0 < k i) (hε : ∀ i, 0 < ε i) (hI : I ⊆ Ici t₀)
    (hbound : ∀ i, ∀ z ∈ E i, mainWallChart (k i) z 0 ≤ -ε i)
    (hy : y ∈ axisFamilyHittingDomain A B h k t₀ E I) :
    IsLeast (axisFamilyHittingTimes A B h k t₀ E I y) (C.firstTime E I y) := by
  obtain ⟨t, ht⟩ := exists_axisFamily_first_time A B hh hk hε hI hbound hy
  rwa [C.firstTime_of_isLeast hI ht]

end AxisWallAtlasFamily

/-- A measurable real-valued extension agrees with the genuine earliest target hit on its domain. -/
theorem exists_measurable_axisFamily_firstTime {ι : Type*} [Finite ι]
    (A : NormalizedSymmetry) (B : ι → NormalizedSymmetry) {h t₀ : ℝ} {k ε : ι → ℝ}
    {E : ι → Set SectionCoordinates} {I : Set ℝ}
    (hh : 0 < h) (hk : ∀ i, 0 < k i) (hε : ∀ i, 0 < ε i) (hI : I ⊆ Ici t₀)
    (hbound : ∀ i, ∀ z ∈ E i, mainWallChart (k i) z 0 ≤ -ε i)
    (hE : ∀ i, MeasurableSet (E i)) (hImeas : MeasurableSet I) :
    ∃ τ : SectionCoordinates → ℝ, Measurable τ ∧
      ∀ y ∈ axisFamilyHittingDomain A B h k t₀ E I,
        IsLeast (axisFamilyHittingTimes A B h k t₀ E I y) (τ y) := by
  obtain ⟨C⟩ := exists_axisWallAtlasFamily A B (t₀ := t₀) hh hk
  exact ⟨C.firstTime E I, C.measurable_firstTime hE hImeas,
    fun _ hy => C.firstTime_isLeast hh hk hε hI hbound hy⟩

end BianchiIX
