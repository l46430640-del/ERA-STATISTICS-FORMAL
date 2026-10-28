import BianchiIX.Measure.MainWallPhysicalCapture
import BianchiIX.Statistics.PhysicalFuture

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal

/-- Finite exceptional flux and strict physical return expansion give statistics on almost every infinitely returning orbit. -/
theorem ae_mainWall_statistical_future {h ε η σ Bcap : ℝ} {J : ℕ} {B F : Set SectionCoordinates}
    (hh : 0 < h) (hε : 0 < ε) (hbound : ∀ z ∈ B, mainWallChart h z 0 ≤ -ε)
    (hB : MeasurableSet B) (hF : MeasurableSet F) (hfinite : mainWallMeasure h F ≠ ⊤)
    (hgood : ∀ z ∈ B \ F, StatisticalCoreFuture η J σ Bcap (mainWallChart h z)) :
    ∀ᵐ z ∂mainWallMeasure h, z ∈ mainWallInfiniteReturns h 0 B →
      StatisticalCoreFuture η J σ Bcap (mainWallChart h z) := by
  filter_upwards [ae_mainWall_physical_capture (t₀ := 0) hh hε hbound hB hF hfinite] with z hz hrec
  obtain ⟨t, ht, harr, htarget⟩ := hz hrec
  have hc := mainWallChart_constraint hrec.2.1
  have Hflow := normalizedMaxCurve_forward (mainWallChart_positive hh z) hc ht
  have heq := (mainWallChart_coordinates Hflow.2.1 Hflow.2.2.1 harr.2.2.2 harr.2.2.1).2
  have H := hgood _ htarget
  rw [heq] at H
  exact H.of_forward hc ht

end BianchiIX
