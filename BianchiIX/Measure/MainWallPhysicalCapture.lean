import BianchiIX.Measure.MainWallReturnRecurrence
import BianchiIX.Measure.MainWallReturnCapture

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal

def mainWallInfiniteReturns (h t₀ : ℝ) (B : Set SectionCoordinates) : Set SectionCoordinates :=
  {y | y ∈ B ∧ y ∈ mainWallChartDomain h ∧
    (mainWallHittingTimes h h t₀ B (Ioi t₀) y).Infinite}

theorem measurableSet_mainWallInfiniteReturns {h t₀ ε : ℝ} {B : Set SectionCoordinates}
    (hh : 0 < h) (hε : 0 < ε) (hbound : ∀ z ∈ B, mainWallChart h z 0 ≤ -ε)
    (hB : MeasurableSet B) : MeasurableSet (mainWallInfiniteReturns h t₀ B) := by
  obtain ⟨R, _, hR, _, _, hfirst, _, _⟩ := exists_mainWall_firstReturn (t₀ := t₀) hh hε hbound hB
  obtain ⟨τ, _, hτ⟩ := exists_measurable_mainWall_returnTime (t₀ := t₀) hh hε hbound hB
  have hRtime := fun y hy => mainWall_firstReturn_eq_at_returnTime hfirst hτ (y := y) hy
  have hD := measurableSet_mainWallReturnDomain (t₀ := t₀) hh hB
  have hall : MeasurableSet {y | ∀ n : ℕ, R^[n] y ∈ mainWallReturnDomain h t₀ B} := by
    simp only [ofPred_forall]
    exact MeasurableSet.iInter (fun n => hD.preimage (hR.iterate n))
  convert! hall using 1
  ext y
  constructor
  · intro hy
    exact (mainWall_return_iterates_iff_infinite_hits hh hε hbound hτ hRtime hy.1 hy.2.1).mpr hy.2.2
  · intro hy
    have hyB : y ∈ B := by simpa using (hy 0).1
    have hychart : y ∈ mainWallChartDomain h := by simpa using (hτ _ (hy 0)).1.2.1.1
    exact ⟨hyB, hychart,
      (mainWall_return_iterates_iff_infinite_hits hh hε hbound hτ hRtime hyB hychart).mp hy⟩

/-- Capture stated entirely in terms of actual orbit intersections, without a total return-map extension. -/
theorem ae_mainWall_physical_capture {h t₀ ε : ℝ} {B E : Set SectionCoordinates}
    (hh : 0 < h) (hε : 0 < ε) (hbound : ∀ z ∈ B, mainWallChart h z 0 ≤ -ε)
    (hB : MeasurableSet B) (hE : MeasurableSet E) (hfinite : mainWallMeasure h E ≠ ∞) :
    ∀ᵐ y ∂mainWallMeasure h, y ∈ mainWallInfiniteReturns h t₀ B →
      ∃ t ≥ t₀, (y, t) ∈ mainWallArrivalRelation h h t₀ ∧
        mainWallCoordinates (normalizedMaxCurve (mainWallChart h y) t₀ t) ∈ B \ E := by
  obtain ⟨R, _, _, hfirst, hcapture⟩ := exists_mainWall_firstReturn_capture (t₀ := t₀) hh hε hbound hB
  obtain ⟨τ, _, hτ⟩ := exists_measurable_mainWall_returnTime (t₀ := t₀) hh hε hbound hB
  have hRtime := fun y hy => mainWall_firstReturn_eq_at_returnTime hfirst hτ (y := y) hy
  filter_upwards [(hcapture E hE hfinite).2] with y hy hrec
  have hvalid := (mainWall_return_iterates_iff_infinite_hits hh hε hbound hτ hRtime hrec.1 hrec.2.1).mpr hrec.2.2
  obtain ⟨n, hn⟩ := hy hvalid
  obtain ⟨hle, hstate⟩ := mainWall_return_iterate_state hh hτ hRtime hrec.2.1 n (fun i _ => hvalid i)
  refine ⟨cumulativeReturnTime R τ t₀ n y, hle, ⟨hrec.2.1, ?_, ?_, ?_⟩, ?_⟩
  · exact normalizedMaxDomain_contains_Ici (mainWallChart_positive hh y)
      (mainWallChart_constraint hrec.2.1) t₀ hle
  · rw [← hstate]
    rfl
  · rw [← hstate]
    exact mainWallChart_negative (hτ _ (hvalid n)).1.2.1.1
  · rw [← hstate, mainWallCoordinates_chart]
    exact ⟨(hvalid n).1, hn⟩

end BianchiIX
