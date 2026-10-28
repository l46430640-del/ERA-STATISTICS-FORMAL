import BianchiIX.Measure.AxisReturnMeasure
import BianchiIX.Measure.MainWallFirstTime
import BianchiIX.Measure.Capture

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal

theorem exists_axisFamily_firstReturn_capture {ι : Type*} [Finite ι] [Encodable ι] [Nonempty ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι] (B : ι → NormalizedSymmetry)
    {k ε : ι → ℝ} {t₀ : ℝ} {E : ι → Set SectionCoordinates}
    (hk : ∀ i, 0 < k i) (hε : ∀ i, 0 < ε i)
    (hbound : ∀ i, ∀ z ∈ E i, mainWallChart (k i) z 0 ≤ -ε i)
    (hE : ∀ i, MeasurableSet (E i)) (hcharts : InjOn (axisFamilyChart B k) (axisFamilySection E)) :
    ∃ R : ι × SectionCoordinates → ι × SectionCoordinates,
      Measurable R ∧ InjOn R (axisFamilyReturnDomain B k t₀ E) ∧
      (∀ z ∈ axisFamilyReturnDomain B k t₀ E, ∃ t,
        IsLeast (axisFamilyReturnTimes B k t₀ E z) t ∧
        axisFamilyChart B k (R z) = normalizedMaxCurve (axisFamilyChart B k z) t₀ t ∧
        R z ∈ axisFamilySection E) ∧
      ∀ F, MeasurableSet F → axisFamilyMeasure k F ≠ ∞ →
        axisFamilyMeasure k (permanentFailure R (axisFamilyReturnDomain B k t₀ E) F) = 0 ∧
        ∀ᵐ z ∂axisFamilyMeasure k, (∀ n : ℕ, R^[n] z ∈ axisFamilyReturnDomain B k t₀ E) →
          ∃ n : ℕ, R^[n] z ∉ F := by
  obtain ⟨R, j, hR, hj, hinj, hfirst, hexpand, hchange⟩ :=
    exists_axisFamily_firstReturn B (t₀ := t₀) hk hε hbound hE hcharts
  have hD := measurableSet_axisFamilyReturnDomain B (t₀ := t₀) hk hE
  have hexpand' := fun z hz => (hexpand z hz).1
  have hchange' := fun S hS hSD => (hchange S hS hSD).2
  exact ⟨R, hR, hinj, hfirst, fun F hF hfinite =>
    ⟨permanentFailure_null hR hD hF hfinite hj hexpand' hchange',
      ae_eventually_leaves_failure hR hD hF hfinite hj hexpand' hchange'⟩⟩

/-- The small-section inequalities prove both physical disjointness and the transverse shear margin. -/
theorem exists_smallAxis_firstReturn_capture {h t₀ : ℝ} {E : Fin 3 → Set SectionCoordinates}
    (hh : 0 < h) (hh1 : h ≤ 1 / 8) (hE : ∀ i, MeasurableSet (E i))
    (hsmall : ∀ i, ∀ y ∈ E i, y ∈ mainWallChartDomain h ∧ |y 0| ≤ 1 / 8 ∧
      Real.exp (-y 1) ≤ h / 8 ∧ Real.exp (-y 2) ≤ h / 8) :
    ∃ R : Fin 3 × SectionCoordinates → Fin 3 × SectionCoordinates,
      Measurable R ∧ InjOn R (axisFamilyReturnDomain primaryAxisFrame (fun _ => h) t₀ E) ∧
      (∀ z ∈ axisFamilyReturnDomain primaryAxisFrame (fun _ => h) t₀ E, ∃ t,
        IsLeast (axisFamilyReturnTimes primaryAxisFrame (fun _ => h) t₀ E z) t ∧
        axisFamilyChart primaryAxisFrame (fun _ => h) (R z) =
          normalizedMaxCurve (axisFamilyChart primaryAxisFrame (fun _ => h) z) t₀ t ∧
        R z ∈ axisFamilySection E) ∧
      ∀ F, MeasurableSet F → axisFamilyMeasure (fun _ : Fin 3 => h) F ≠ ∞ →
        axisFamilyMeasure (fun _ : Fin 3 => h)
          (permanentFailure R (axisFamilyReturnDomain primaryAxisFrame (fun _ => h) t₀ E) F) = 0 ∧
        ∀ᵐ z ∂axisFamilyMeasure (fun _ : Fin 3 => h),
          (∀ n : ℕ, R^[n] z ∈ axisFamilyReturnDomain primaryAxisFrame (fun _ => h) t₀ E) →
            ∃ n : ℕ, R^[n] z ∉ F := by
  have hbound (i : Fin 3) (y : SectionCoordinates) (hy : y ∈ E i) :
      mainWallChart h y 0 ≤ -(15 / 16) :=
    mainWall_small_target_shear hh hh1 (hsmall i y hy).1 (hsmall i y hy).2.1
      (hsmall i y hy).2.2.1 (hsmall i y hy).2.2.2
  have hdom (i : Fin 3) : E i ⊆ dominantWallChartDomain h := fun y hy =>
    mem_dominantWallChartDomain_of_small hh (hsmall i y hy).1
      (hsmall i y hy).2.2.1 (hsmall i y hy).2.2.2
  exact exists_axisFamily_firstReturn_capture primaryAxisFrame (fun _ => hh)
    (fun _ => by norm_num : ∀ _ : Fin 3, (0 : ℝ) < 15 / 16) hbound hE (primaryAxisChart_injOn hdom)

end BianchiIX
