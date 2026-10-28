import BianchiIX.Measure.GlobalWallFirstTime
import BianchiIX.Measure.AxisPhysicalCapture

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal

def axisFamilySuccessTargets {ι : Type*} (E : ι → Set SectionCoordinates)
    (F : Set (ι × SectionCoordinates)) (i : ι) : Set SectionCoordinates :=
  E i \ (Prod.mk i ⁻¹' F)

theorem measurableSet_axisFamilySuccessTargets {ι : Type*} [MeasurableSpace ι]
    {E : ι → Set SectionCoordinates} {F : Set (ι × SectionCoordinates)}
    (hE : ∀ i, MeasurableSet (E i)) (hF : MeasurableSet F) (i : ι) :
    MeasurableSet (axisFamilySuccessTargets E F i) :=
  (hE i).diff (hF.preimage (measurable_const.prodMk measurable_id))

theorem globalAxisWallHittingTimes_success {ι : Type*} (A : ι → NormalizedSymmetry)
    (h : ι → ℝ) (E : ι → Set SectionCoordinates) (F : Set (ι × SectionCoordinates))
    (I : Set ℝ) (x : NormalizedState) :
    globalAxisWallHittingTimes A h (axisFamilySuccessTargets E F) I x =
      {t | t ∈ I ∧ t ∈ normalizedMaxDomain x 0 ∧ ∃ z ∈ axisFamilySection E \ F,
        axisFamilyChart A h z = normalizedMaxCurve x 0 t} := by
  ext t
  constructor
  · rintro ⟨htI, ht, i, y, hy, heq⟩
    exact ⟨htI, ht, (i, y), hy, heq⟩
  · rintro ⟨htI, ht, ⟨i, y⟩, hy, heq⟩
    exact ⟨htI, ht, i, y, hy, heq⟩

theorem ae_smallAxis_success_hitting {h : ℝ} {E : Fin 3 → Set SectionCoordinates}
    {F : Set (Fin 3 × SectionCoordinates)} (hh : 0 < h) (hh1 : h ≤ 1 / 8)
    (hE : ∀ i, MeasurableSet (E i))
    (hsmall : ∀ i, ∀ y ∈ E i, y ∈ mainWallChartDomain h ∧ |y 0| ≤ 1 / 8 ∧
      Real.exp (-y 1) ≤ h / 8 ∧ Real.exp (-y 2) ≤ h / 8)
    (hF : MeasurableSet F) (hfinite : axisFamilyMeasure (fun _ : Fin 3 => h) F ≠ ∞) :
    ∀ᵐ z ∂axisFamilyMeasure (fun _ : Fin 3 => h),
      z ∈ axisFamilyInfiniteReturns primaryAxisFrame (fun _ => h) 0 E →
        axisFamilyChart primaryAxisFrame (fun _ => h) z ∈
          globalAxisWallHittingDomain primaryAxisFrame (fun _ => h)
            (axisFamilySuccessTargets E F) (Ici 0) := by
  filter_upwards [ae_smallAxis_physical_capture (t₀ := 0) hh hh1 hE hsmall hF hfinite] with z hz hrec
  obtain ⟨t, ht, w, hw, heq⟩ := hz hrec
  have hpos := axisWallChart_positive (primaryAxisFrame z.1) hh z.2
  have hcon := axisWallChart_constraint (primaryAxisFrame z.1) (hsmall z.1 z.2 hrec.1).1
  exact ⟨t, ht, normalizedMaxDomain_contains_Ici hpos hcon 0 ht, w.1, w.2, hw, heq⟩

/-- One Borel first-success pair works for every physical initial state that reaches the target. -/
theorem exists_smallAxis_borel_first_success {h : ℝ} {E : Fin 3 → Set SectionCoordinates}
    {F : Set (Fin 3 × SectionCoordinates)} (hh : 0 < h) (hh1 : h ≤ 1 / 8)
    (hE : ∀ i, MeasurableSet (E i))
    (hsmall : ∀ i, ∀ y ∈ E i, y ∈ mainWallChartDomain h ∧ |y 0| ≤ 1 / 8 ∧
      Real.exp (-y 1) ≤ h / 8 ∧ Real.exp (-y 2) ≤ h / 8)
    (hF : MeasurableSet F) (hfinite : axisFamilyMeasure (fun _ : Fin 3 => h) F ≠ ∞) :
    ∃ τ : NormalizedState → ℝ, ∃ Y : NormalizedState → NormalizedState,
      Measurable τ ∧ Measurable Y ∧ (∀ x, Y x = normalizedMaxCurve x 0 (τ x)) ∧
      (∀ x, positiveWalls x → stateConstraint x = 1 →
        x ∈ globalAxisWallHittingDomain primaryAxisFrame (fun _ => h)
          (axisFamilySuccessTargets E F) (Ici 0) →
        IsLeast (globalAxisWallHittingTimes primaryAxisFrame (fun _ => h)
          (axisFamilySuccessTargets E F) (Ici 0) x) (τ x) ∧
          ∃ w ∈ axisFamilySection E \ F, axisFamilyChart primaryAxisFrame (fun _ => h) w = Y x) ∧
      (∀ᵐ z ∂axisFamilyMeasure (fun _ : Fin 3 => h),
        z ∈ axisFamilyInfiniteReturns primaryAxisFrame (fun _ => h) 0 E →
          let x := axisFamilyChart primaryAxisFrame (fun _ => h) z
          IsLeast (globalAxisWallHittingTimes primaryAxisFrame (fun _ => h)
            (axisFamilySuccessTargets E F) (Ici 0) x) (τ x) ∧
            ∃ w ∈ axisFamilySection E \ F, axisFamilyChart primaryAxisFrame (fun _ => h) w = Y x) := by
  let B := axisFamilySuccessTargets E F
  let τ := globalAxisWallFirstTime primaryAxisFrame (fun _ => h) B (Ici 0)
  let Y := globalAxisWallFirstState primaryAxisFrame (fun _ => h) B (Ici 0)
  have hB := measurableSet_axisFamilySuccessTargets hE hF
  have hchart (i : Fin 3) : B i ⊆ mainWallChartDomain h := fun y hy => (hsmall i y hy.1).1
  have hfirst (x : NormalizedState) (hp : positiveWalls x) (hc : stateConstraint x = 1)
      (hx : x ∈ globalAxisWallHittingDomain primaryAxisFrame (fun _ => h) B (Ici 0)) :
      IsLeast (globalAxisWallHittingTimes primaryAxisFrame (fun _ => h) B (Ici 0) x) (τ x) ∧
        ∃ w ∈ axisFamilySection E \ F, axisFamilyChart primaryAxisFrame (fun _ => h) w = Y x := by
    have H := globalAxisWallFirstTime_small_target primaryAxisFrame (fun _ => hh) (fun _ => hh1)
      hp hc (Subset.refl _) (fun i y hy => hsmall i y hy.1) hx
    obtain ⟨i, y, hy, heq⟩ := H.1.2.2
    exact ⟨H, (i, y), hy, heq⟩
  refine ⟨τ, Y, measurable_globalAxisWallFirstTime primaryAxisFrame (fun _ => hh) hB measurableSet_Ici hchart,
    measurable_globalAxisWallFirstState primaryAxisFrame (fun _ => hh) hB measurableSet_Ici hchart,
    fun _ => rfl, hfirst, ?_⟩
  filter_upwards [ae_smallAxis_success_hitting hh hh1 hE hsmall hF hfinite] with z hz hrec
  exact hfirst _ (axisWallChart_positive (primaryAxisFrame z.1) hh z.2)
    (axisWallChart_constraint (primaryAxisFrame z.1) (hsmall z.1 z.2 hrec.1).1) (hz hrec)

end BianchiIX
