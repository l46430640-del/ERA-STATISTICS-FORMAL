import BianchiIX.Measure.MainWallReturnMeasure
import BianchiIX.Measure.Capture

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal

/-- Capture for actual first returns; the only measure bound is on the chosen failure set. -/
theorem exists_mainWall_firstReturn_capture {h t₀ ε : ℝ} {B : Set SectionCoordinates}
    (hh : 0 < h) (hε : 0 < ε) (hbound : ∀ z ∈ B, mainWallChart h z 0 ≤ -ε)
    (hB : MeasurableSet B) :
    ∃ R : SectionCoordinates → SectionCoordinates,
      Measurable R ∧ InjOn R (mainWallReturnDomain h t₀ B) ∧
      (∀ y ∈ mainWallReturnDomain h t₀ B, ∃ t,
        IsLeast (mainWallHittingTimes h h t₀ B (Ioi t₀) y) t ∧
        R y = mainWallCoordinates (normalizedMaxCurve (mainWallChart h y) t₀ t)) ∧
      ∀ E, MeasurableSet E → mainWallMeasure h E ≠ ∞ →
        mainWallMeasure h (permanentFailure R (mainWallReturnDomain h t₀ B) E) = 0 ∧
        ∀ᵐ y ∂mainWallMeasure h, (∀ n : ℕ, R^[n] y ∈ mainWallReturnDomain h t₀ B) →
          ∃ n : ℕ, R^[n] y ∉ E := by
  obtain ⟨R, j, hR, hj, hinj, hfirst, hexpand, hchange⟩ :=
    exists_mainWall_firstReturn (t₀ := t₀) hh hε hbound hB
  have hD := measurableSet_mainWallReturnDomain (t₀ := t₀) hh hB
  have hexpand' := fun y hy => (hexpand y hy).1
  have hchange' := fun A hA hAD => (hchange A hA hAD).2
  exact ⟨R, hR, hinj, hfirst, fun E hE hfinite =>
    ⟨permanentFailure_null hR hD hE hfinite hj hexpand' hchange',
      ae_eventually_leaves_failure hR hD hE hfinite hj hexpand' hchange'⟩⟩

end BianchiIX
