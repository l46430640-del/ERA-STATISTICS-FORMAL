import BianchiIX.Measure.AxisPhysicalCapture
import BianchiIX.Statistics.PhysicalFutureAxes

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal

theorem ae_axisFamilyMeasure_iff {ι : Type*} [Countable ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] (k : ι → ℝ) (P : ι × SectionCoordinates → Prop) :
    (∀ᵐ z ∂axisFamilyMeasure k, P z) ↔ ∀ i, ∀ᵐ y ∂mainWallMeasure (k i), P (i, y) := by
  rw [axisFamilyMeasure, Measure.ae_sum_iff]
  exact forall_congr' (fun i => (measurableEmbedding_prodMk_left i).ae_map_iff)

theorem axisFamilyMeasure_constant_section {ι : Type*} [Fintype ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] (h : ℝ) {F : Set SectionCoordinates} (hF : MeasurableSet F) :
    axisFamilyMeasure (fun _ : ι => h) (axisFamilySection (fun _ => F)) =
      (Fintype.card ι : ℝ≥0∞) * mainWallMeasure h F := by
  rw [axisFamilyMeasure_apply _ (measurableSet_axisFamilySection (fun _ => hF))]
  simp [axisFamilySection, tsum_fintype]

/-- Small physical sections may change dominant axes before reaching the statistical core. -/
theorem ae_primaryAxis_statistical_future {h η σ Bcap : ℝ} {J : ℕ}
    {E : Fin 3 → Set SectionCoordinates} {F : Set (Fin 3 × SectionCoordinates)}
    (hh : 0 < h) (hh1 : h ≤ 1 / 8) (hE : ∀ i, MeasurableSet (E i))
    (hsmall : ∀ i, ∀ y ∈ E i, y ∈ mainWallChartDomain h ∧ |y 0| ≤ 1 / 8 ∧
      Real.exp (-y 1) ≤ h / 8 ∧ Real.exp (-y 2) ≤ h / 8)
    (hF : MeasurableSet F) (hfinite : axisFamilyMeasure (fun _ : Fin 3 => h) F ≠ ⊤)
    (hgood : ∀ z ∈ axisFamilySection E \ F, StatisticalCoreFuture η J σ Bcap (mainWallChart h z.2)) :
    ∀ᵐ z ∂axisFamilyMeasure (fun _ : Fin 3 => h),
      z ∈ axisFamilyInfiniteReturns primaryAxisFrame (fun _ => h) 0 E →
        StatisticalCoreFuture η J σ Bcap (axisFamilyChart primaryAxisFrame (fun _ => h) z) := by
  filter_upwards [ae_smallAxis_physical_capture (t₀ := 0) hh hh1 hE hsmall hF hfinite] with z hz hrec
  obtain ⟨t, ht, w, hw, heq⟩ := hz hrec
  have H : StatisticalCoreFuture η J σ Bcap (axisFamilyChart primaryAxisFrame (fun _ => h) w) :=
    (statisticalCoreFuture_axisWallChart_iff (Equiv.swap 0 w.1) w.2).mpr (hgood w hw)
  have hc : stateConstraint (axisFamilyChart primaryAxisFrame (fun _ => h) z) = 1 :=
    axisWallChart_constraint (primaryAxisFrame z.1) (hsmall z.1 z.2 hrec.1).1
  rw [heq] at H
  exact H.of_forward hc ht

end BianchiIX
