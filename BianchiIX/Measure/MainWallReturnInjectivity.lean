import BianchiIX.Measure.MainWallFirstMap
import BianchiIX.Dynamics.FlowInjectivity

noncomputable section

namespace BianchiIX

open Set MeasureTheory

def mainWallReturnDomain (h t₀ : ℝ) (B : Set SectionCoordinates) : Set SectionCoordinates :=
  B ∩ mainWallHittingDomain h h t₀ B (Ioi t₀)

theorem measurableSet_mainWallReturnDomain {h t₀ : ℝ} {B : Set SectionCoordinates}
    (hh : 0 < h) (hB : MeasurableSet B) : MeasurableSet (mainWallReturnDomain h t₀ B) :=
  hB.inter (measurableSet_mainWallHittingDomain hh hh hB measurableSet_Ioi)

theorem mainWallArrivalRelation_chart {h k t₀ t : ℝ} {y : SectionCoordinates}
    (hh : 0 < h) (hy : (y, t) ∈ mainWallArrivalRelation h k t₀) :
    mainWallChart k (mainWallCoordinates (normalizedMaxCurve (mainWallChart h y) t₀ t)) =
      normalizedMaxCurve (mainWallChart h y) t₀ t := by
  have hp := (maximalNormalizedSolution (mainWallChart h y) t₀).physical
    (mainWallChart_positive hh y) (mainWallChart_constraint hy.1) hy.2.1
  exact (mainWallChart_coordinates hp.1 hp.2 hy.2.2.2 hy.2.2.1).2

/-- Two first returns from the same section cannot merge, even if their flight times differ. -/
theorem mainWall_firstReturn_pair_injective {h t₀ s t : ℝ} {B : Set SectionCoordinates}
    {x y : SectionCoordinates} (hh : 0 < h) (hx : x ∈ B) (hy : y ∈ B)
    (hs : IsLeast (mainWallHittingTimes h h t₀ B (Ioi t₀) x) s)
    (ht : IsLeast (mainWallHittingTimes h h t₀ B (Ioi t₀) y) t)
    (heq : mainWallCoordinates (normalizedMaxCurve (mainWallChart h x) t₀ s) =
      mainWallCoordinates (normalizedMaxCurve (mainWallChart h y) t₀ t)) : x = y := by
  have hstate : normalizedMaxCurve (mainWallChart h x) t₀ s =
      normalizedMaxCurve (mainWallChart h y) t₀ t := by
    rw [← mainWallArrivalRelation_chart hh hs.1.2.1,
      ← mainWallArrivalRelation_chart hh ht.1.2.1, heq]
  have hnot {u v : SectionCoordinates} {a b : ℝ} (hu : u ∈ B)
      (ha : IsLeast (mainWallHittingTimes h h t₀ B (Ioi t₀) u) a)
      (hb : IsLeast (mainWallHittingTimes h h t₀ B (Ioi t₀) v) b)
      (hab : a < b)
      (H : normalizedMaxCurve (mainWallChart h u) t₀ a =
        normalizedMaxCurve (mainWallChart h v) t₀ b) : False := by
    have huc := ha.1.2.1.1
    have hvc := hb.1.2.1.1
    have hz := normalizedMaxCurve_eq_at_time_difference
      (mainWallChart_positive hh u) (mainWallChart_constraint huc)
      (mainWallChart_positive hh v) (mainWallChart_constraint hvc) ha.1.1.le hab.le H
    have htime : t₀ + (b - a) ∈ mainWallHittingTimes h h t₀ B (Ioi t₀) v := by
      refine ⟨by change t₀ < t₀ + (b - a); linarith, ⟨hvc, ?_, ?_, ?_⟩, ?_⟩
      · exact normalizedMaxDomain_contains_Ici (mainWallChart_positive hh v)
          (mainWallChart_constraint hvc) t₀ (show t₀ ≤ t₀ + (b - a) by linarith)
      · rw [hz]
        rfl
      · rw [hz]
        exact mainWallChart_negative huc
      · rw [hz, mainWallCoordinates_chart]
        exact hu
    have hmin := hb.2 htime
    have ha0 := ha.1.1
    change t₀ < a at ha0
    linarith
  have hst : s = t := by
    rcases lt_trichotomy s t with hlt | he | hgt
    · exact (hnot hx hs ht hlt hstate).elim
    · exact he
    · exact (hnot hy ht hs hgt hstate.symm).elim
  apply mainWallChart_injective h
  apply normalizedMaxCurve_injOn t₀ s hs.1.2.1.2.1
    (by simpa [hst] using ht.1.2.1.2.1)
  simpa [hst] using hstate

theorem mainWall_firstReturn_injOn {h t₀ : ℝ} {B : Set SectionCoordinates}
    {R : SectionCoordinates → SectionCoordinates} (hh : 0 < h)
    (hfirst : ∀ y ∈ mainWallReturnDomain h t₀ B, ∃ t,
      IsLeast (mainWallHittingTimes h h t₀ B (Ioi t₀) y) t ∧
      R y = mainWallCoordinates (normalizedMaxCurve (mainWallChart h y) t₀ t)) :
    InjOn R (mainWallReturnDomain h t₀ B) := by
  intro x hx y hy heq
  obtain ⟨s, hs, hRx⟩ := hfirst x hx
  obtain ⟨t, ht, hRy⟩ := hfirst y hy
  exact mainWall_firstReturn_pair_injective hh hx.1 hy.1 hs ht (hRx.symm.trans (heq.trans hRy))

end BianchiIX
