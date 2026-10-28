import BianchiIX.Measure.WallSaturation
import BianchiIX.Analysis.SectionCrossings

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal

def globalAxisWallHittingTimes {ι : Type*} (A : ι → NormalizedSymmetry) (h : ι → ℝ)
    (B : ι → Set SectionCoordinates) (I : Set ℝ) (x : NormalizedState) : Set ℝ :=
  {t | t ∈ I ∧ t ∈ normalizedMaxDomain x 0 ∧
    ∃ i, ∃ y ∈ B i, axisWallChart (A i) (h i) y = normalizedMaxCurve x 0 t}

def globalAxisWallHittingDomain {ι : Type*} (A : ι → NormalizedSymmetry) (h : ι → ℝ)
    (B : ι → Set SectionCoordinates) (I : Set ℝ) : Set NormalizedState :=
  {x | (globalAxisWallHittingTimes A h B I x).Nonempty}

/-- Inverting actual orbit segments avoids projecting an uncountable family of event graphs. -/
theorem globalAxisWallHittingDomain_eq_image {ι : Type*} (A : ι → NormalizedSymmetry)
    {h : ι → ℝ} {B : ι → Set SectionCoordinates} (I : Set ℝ)
    (hchart : ∀ i, B i ⊆ mainWallChartDomain (h i)) :
    globalAxisWallHittingDomain A h B I = ⋃ i, axisWallFlowMap (A i) (h i) ''
      {p | p.1 ∈ B i ∧ p ∈ axisWallFlowDomain (A i) (h i) ∧ -p.2 ∈ I} := by
  ext x
  constructor
  · rintro ⟨t, htI, ht, i, y, hy, heq⟩
    have H := normalizedMaxCurve_inverse ht
    rw [← heq] at H
    exact mem_iUnion.mpr ⟨i, (y, -t), ⟨hy, ⟨hchart i hy, H.1⟩, by simpa using htI⟩, H.2⟩
  · intro hx
    obtain ⟨i, p, hp, rfl⟩ := mem_iUnion.mp hx
    have H := normalizedMaxCurve_inverse hp.2.1.2
    exact ⟨-p.2, hp.2.2, H.1, i, p.1, hp.1, H.2.symm⟩

theorem measurableSet_globalAxisWallHittingDomain {ι : Type*} [Countable ι]
    (A : ι → NormalizedSymmetry) {h : ι → ℝ} {B : ι → Set SectionCoordinates} {I : Set ℝ}
    (hh : ∀ i, 0 < h i) (hB : ∀ i, MeasurableSet (B i)) (hI : MeasurableSet I)
    (hchart : ∀ i, B i ⊆ mainWallChartDomain (h i)) :
    MeasurableSet (globalAxisWallHittingDomain A h B I) := by
  rw [globalAxisWallHittingDomain_eq_image A I hchart]
  apply MeasurableSet.iUnion
  intro i
  apply measurableSet_axisWallFlowMap_image (A i) (hh i)
  · exact (hB i |>.preimage measurable_fst).inter
      ((isOpen_axisWallFlowDomain (A i) (h i)).measurableSet.inter
        (hI.preimage measurable_snd.neg))
  · exact fun _ hp => hp.2.1

def globalAxisWallFirstDelay {ι : Type*} (A : ι → NormalizedSymmetry) (h : ι → ℝ)
    (B : ι → Set SectionCoordinates) (I : Set ℝ) (x : NormalizedState) : ℝ≥0∞ :=
  ⨅ t : globalAxisWallHittingTimes A h B I x, ENNReal.ofReal t.val

theorem globalAxisWallFirstDelay_lt_iff {ι : Type*} (A : ι → NormalizedSymmetry)
    (h : ι → ℝ) (B : ι → Set SectionCoordinates) (I : Set ℝ) (x : NormalizedState) (r : ℝ≥0∞) :
    globalAxisWallFirstDelay A h B I x < r ↔
      x ∈ globalAxisWallHittingDomain A h B (I ∩ {t | ENNReal.ofReal t < r}) := by
  simp only [globalAxisWallFirstDelay, iInf_lt_iff, globalAxisWallHittingDomain,
    globalAxisWallHittingTimes, mem_ofPred_eq, Set.Nonempty, mem_inter_iff]
  constructor
  · rintro ⟨⟨t, htI, ht, hy⟩, hr⟩
    exact ⟨t, ⟨htI, hr⟩, ht, hy⟩
  · rintro ⟨t, ⟨htI, hr⟩, ht, hy⟩
    exact ⟨⟨t, htI, ht, hy⟩, hr⟩

theorem measurable_globalAxisWallFirstDelay {ι : Type*} [Countable ι]
    (A : ι → NormalizedSymmetry) {h : ι → ℝ} {B : ι → Set SectionCoordinates} {I : Set ℝ}
    (hh : ∀ i, 0 < h i) (hB : ∀ i, MeasurableSet (B i)) (hI : MeasurableSet I)
    (hchart : ∀ i, B i ⊆ mainWallChartDomain (h i)) :
    Measurable (globalAxisWallFirstDelay A h B I) := by
  apply measurable_of_Iio
  intro r
  have heq : globalAxisWallFirstDelay A h B I ⁻¹' Iio r =
      globalAxisWallHittingDomain A h B (I ∩ {t | ENNReal.ofReal t < r}) := by
    ext x
    exact globalAxisWallFirstDelay_lt_iff A h B I x r
  rw [heq]
  exact measurableSet_globalAxisWallHittingDomain A hh hB
    (hI.inter (measurableSet_lt ENNReal.measurable_ofReal measurable_const)) hchart

theorem globalAxisWallFirstDelay_lt_top_iff {ι : Type*} (A : ι → NormalizedSymmetry)
    (h : ι → ℝ) (B : ι → Set SectionCoordinates) (I : Set ℝ) (x : NormalizedState) :
    globalAxisWallFirstDelay A h B I x < ⊤ ↔ x ∈ globalAxisWallHittingDomain A h B I := by
  simpa using globalAxisWallFirstDelay_lt_iff A h B I x ⊤

theorem finite_globalAxisWallHittingTimes {ι : Type*} [Finite ι]
    (A : ι → NormalizedSymmetry) {h ε : ι → ℝ} {B : ι → Set SectionCoordinates} {I : Set ℝ}
    {x : NormalizedState} {T : ℝ} (hh : ∀ i, 0 < h i) (hε : ∀ i, 0 < ε i)
    (hp : positiveWalls x) (hc : stateConstraint x = 1)
    (hbound : ∀ i, ∀ y ∈ B i, mainWallChart (h i) y 0 ≤ -ε i) :
    (globalAxisWallHittingTimes A h B I x ∩ Icc 0 T).Finite := by
  let α := fun i => normalizedMaxCurve ((A i).map x) 0
  have hderiv (i : ι) (t : ℝ) (ht : t ∈ Icc 0 T) :=
    hasDerivAt_normalized_components (hasDerivAt_normalizedMaxCurve
      (normalizedMaxDomain_contains_Ici ((A i).positive x |>.mpr hp)
        ((A i).constraint x |>.trans hc) 0 ht.1))
  have hf (i : ι) : {t ∈ Icc 0 T | α i t 2 = h i ∧ α i t 0 ≤ -ε i}.Finite :=
    finite_negative_section_times isCompact_Icc
      (fun t ht => (hderiv i t ht).2.2.1.continuousAt.continuousWithinAt)
      (fun t ht => (hderiv i t ht).1.continuousAt.continuousWithinAt)
      (hh i) (hε i) (fun t ht => (hderiv i t ht).2.2.1)
  apply (Set.finite_iUnion hf).subset
  rintro t ⟨⟨_, ht, i, y, hy, heq⟩, htK⟩
  have he : α i t = mainWallChart (h i) y := by
    rw [show α i t = (A i).map (normalizedMaxCurve x 0 t) from (A i).maxCurve ht,
      ← heq, axisWallChart, ContinuousLinearEquiv.apply_symm_apply]
  exact mem_iUnion.mpr ⟨i, htK, by rw [he]; rfl, by rw [he]; exact hbound i y hy⟩

theorem exists_globalAxisWall_first_time {ι : Type*} [Finite ι]
    (A : ι → NormalizedSymmetry) {h ε : ι → ℝ} {B : ι → Set SectionCoordinates} {I : Set ℝ}
    {x : NormalizedState} (hh : ∀ i, 0 < h i) (hε : ∀ i, 0 < ε i)
    (hp : positiveWalls x) (hc : stateConstraint x = 1) (hI : I ⊆ Ici 0)
    (hbound : ∀ i, ∀ y ∈ B i, mainWallChart (h i) y 0 ≤ -ε i)
    (hx : x ∈ globalAxisWallHittingDomain A h B I) :
    ∃ t, IsLeast (globalAxisWallHittingTimes A h B I x) t :=
  exists_least_of_finite_initial_intervals (fun _ ht => hI ht.1) hx
    (fun _ => finite_globalAxisWallHittingTimes A hh hε hp hc hbound)

theorem globalAxisWallFirstDelay_of_isLeast {ι : Type*} (A : ι → NormalizedSymmetry)
    {h : ι → ℝ} {B : ι → Set SectionCoordinates} {I : Set ℝ} {x : NormalizedState} {t : ℝ}
    (ht : IsLeast (globalAxisWallHittingTimes A h B I x) t) :
    globalAxisWallFirstDelay A h B I x = ENNReal.ofReal t := by
  unfold globalAxisWallFirstDelay
  apply le_antisymm
  · exact iInf_le (fun u : globalAxisWallHittingTimes A h B I x => ENNReal.ofReal u.val) ⟨t, ht.1⟩
  · exact le_iInf fun u => ENNReal.ofReal_le_ofReal (ht.2 u.property)

end BianchiIX
