import BianchiIX.Measure.MainWallHitting
import BianchiIX.Analysis.SectionCrossings

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal

def mainWallHittingTimes (h k t₀ : ℝ) (B : Set SectionCoordinates) (I : Set ℝ)
    (y : SectionCoordinates) : Set ℝ :=
  {t | t ∈ I ∧ (y, t) ∈ mainWallArrivalRelation h k t₀ ∧
    mainWallCoordinates (normalizedMaxCurve (mainWallChart h y) t₀ t) ∈ B}

theorem finite_mainWallHittingTimes {h k t₀ T ε : ℝ} {B : Set SectionCoordinates} {I : Set ℝ}
    {y : SectionCoordinates} (hh : 0 < h) (hk : 0 < k) (hε : 0 < ε)
    (hy : y ∈ mainWallChartDomain h)
    (hB : ∀ z ∈ B, mainWallChart k z 0 ≤ -ε) :
    (mainWallHittingTimes h k t₀ B I y ∩ Icc t₀ T).Finite := by
  let α := normalizedMaxCurve (mainWallChart h y) t₀
  have hpos := mainWallChart_positive hh y
  have hcon := mainWallChart_constraint hy
  have hderiv (t : ℝ) (ht : t ∈ Icc t₀ T) :=
    hasDerivAt_normalized_components (hasDerivAt_normalizedMaxCurve
      (normalizedMaxDomain_contains_Ici hpos hcon t₀ ht.1))
  have hfinite := finite_negative_section_times (K := Icc t₀ T)
    (a := fun t => α t 2) (p := fun t => α t 0) (s := fun t => α t 1)
    isCompact_Icc (fun t ht => (hderiv t ht).2.2.1.continuousAt.continuousWithinAt)
    (fun t ht => (hderiv t ht).1.continuousAt.continuousWithinAt) hk hε
    (fun t ht => (hderiv t ht).2.2.1)
  apply hfinite.subset
  rintro t ⟨ht, htK⟩
  have hphysical := (maximalNormalizedSolution (mainWallChart h y) t₀).physical hpos hcon ht.2.1.2.1
  have hc := mainWallChart_coordinates hphysical.1 hphysical.2 ht.2.1.2.2.2 ht.2.1.2.2.1
  refine ⟨htK, ht.2.1.2.2.1, ?_⟩
  have H := hB _ ht.2.2
  have heq : mainWallChart k (mainWallCoordinates (α t)) = α t := by
    convert! hc.2 using 1
  rw [heq] at H
  exact H

/-- No closedness of the target is needed: finite intersections with bounded time intervals suffice. -/
theorem exists_mainWall_first_time {h k t₀ ε : ℝ} {B : Set SectionCoordinates} {I : Set ℝ}
    {y : SectionCoordinates} (hh : 0 < h) (hk : 0 < k) (hε : 0 < ε)
    (hI : I ⊆ Ici t₀) (hB : ∀ z ∈ B, mainWallChart k z 0 ≤ -ε)
    (hy : y ∈ mainWallHittingDomain h k t₀ B I) :
    ∃ t, IsLeast (mainWallHittingTimes h k t₀ B I y) t := by
  have hsource : y ∈ mainWallChartDomain h := by
    obtain ⟨t, _, ht, _⟩ := hy
    exact ht.1
  exact exists_least_of_finite_initial_intervals (fun _ ht => hI ht.1) hy
    (fun _ => finite_mainWallHittingTimes hh hk hε hsource hB)

theorem mainWall_small_target_shear {k : ℝ} {z : SectionCoordinates}
    (hk : 0 < k) (hk1 : k ≤ 1 / 8) (hz : z ∈ mainWallChartDomain k)
    (hs : |z 0| ≤ 1 / 8) (hb : Real.exp (-z 1) ≤ k / 8) (hc : Real.exp (-z 2) ≤ k / 8) :
    mainWallChart k z 0 ≤ -(15 / 16) := by
  simpa only [neg_div] using (small_section_bounds hk hk1 (Real.exp_pos _).le (Real.exp_pos _).le hb hc hs
    (mainWallChart_negative hz) (mainWallChart_constraint hz)).2.2.1

namespace MainWallArrivalAtlas

variable {h k t₀ : ℝ} (C : MainWallArrivalAtlas h k t₀)

theorem firstDelay_of_isLeast {B : Set SectionCoordinates} {I : Set ℝ} {y : SectionCoordinates}
    {t : ℝ} (ht : IsLeast (mainWallHittingTimes h k t₀ B I y) t) :
    C.firstDelay B I y = ENNReal.ofReal (t - t₀) ∧
      ∃ n, y ∈ (C.branch n).eligible B I ∧ (C.branch n).coordinateTime y = t := by
  classical
  obtain ⟨n, hyn, hn⟩ := (C.mem_relation_iff y t).mp ht.1.2.1
  have heligible : y ∈ (C.branch n).eligible B I := by
    refine ⟨hyn, ?_, ?_⟩
    · rw [hn]
      exact ht.1.1
    · rw [(C.branch n).map_eq_coordinates hyn, hn]
      exact ht.1.2.2
  refine ⟨le_antisymm ?_ ?_, n, heligible, hn⟩
  · calc
      C.firstDelay B I y ≤ (C.branch n).delay B I y := iInf_le _ n
      _ = ENNReal.ofReal (t - t₀) := by rw [(C.branch n).delay_of_mem heligible, hn]
  · apply le_iInf
    intro m
    by_cases hym : y ∈ (C.branch m).eligible B I
    · rw [(C.branch m).delay_of_mem hym]
      apply ENNReal.ofReal_le_ofReal
      apply sub_le_sub_right
      apply ht.2
      refine ⟨hym.2.1, (C.branch m).mem_relation hym.1, ?_⟩
      rw [← (C.branch m).map_eq_coordinates hym.1]
      exact hym.2.2
    · simp [MainWallArrival.delay, hym]

theorem exists_firstDelay_branch {ε : ℝ} {B : Set SectionCoordinates} {I : Set ℝ}
    {y : SectionCoordinates} (hh : 0 < h) (hk : 0 < k) (hε : 0 < ε)
    (hI : I ⊆ Ici t₀) (hB : ∀ z ∈ B, mainWallChart k z 0 ≤ -ε)
    (hy : y ∈ mainWallHittingDomain h k t₀ B I) :
    ∃ n, y ∈ (C.branch n).eligible B I ∧
      (C.branch n).delay B I y = C.firstDelay B I y ∧
      IsLeast (mainWallHittingTimes h k t₀ B I y) ((C.branch n).coordinateTime y) := by
  obtain ⟨t, ht⟩ := exists_mainWall_first_time hh hk hε hI hB hy
  obtain ⟨hfirst, n, hyn, hn⟩ := C.firstDelay_of_isLeast ht
  refine ⟨n, hyn, ?_, ?_⟩
  · rw [(C.branch n).delay_of_mem hyn, hn, hfirst]
  · rwa [hn]

end MainWallArrivalAtlas

end BianchiIX
