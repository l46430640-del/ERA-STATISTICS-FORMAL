import BianchiIX.Measure.IteratedTransport
import BianchiIX.Measure.AxisReturnMeasure
import BianchiIX.Measure.AxisReturnOrbits

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal

/-- Finite products and original-orbit endpoints for the actual cross-axis first return. -/
theorem exists_axisFamily_finiteReturn_transport {ι : Type*} [Finite ι] [Encodable ι] [Nonempty ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι] (B : ι → NormalizedSymmetry)
    {k ε : ι → ℝ} {t₀ : ℝ} {E : ι → Set SectionCoordinates}
    (hk : ∀ i, 0 < k i) (hε : ∀ i, 0 < ε i)
    (hbound : ∀ i, ∀ z ∈ E i, mainWallChart (k i) z 0 ≤ -ε i)
    (hE : ∀ i, MeasurableSet (E i)) (hcharts : InjOn (axisFamilyChart B k) (axisFamilySection E)) :
    ∃ (R : ι × SectionCoordinates → ι × SectionCoordinates)
      (j : ι × SectionCoordinates → ℝ≥0∞) (τ : ι × SectionCoordinates → ℝ),
      Measurable R ∧ Measurable j ∧ Measurable τ ∧
      (∀ z ∈ axisFamilyReturnDomain B k t₀ E,
        IsLeast (axisFamilyReturnTimes B k t₀ E z) (τ z) ∧
        axisFamilyChart B k (R z) = normalizedMaxCurve (axisFamilyChart B k z) t₀ (τ z) ∧
        R z ∈ axisFamilySection E) ∧
      ∀ n : ℕ,
        MeasurableSet (finiteReturnDomain R (axisFamilyReturnDomain B k t₀ E) n) ∧
        InjOn (R^[n]) (finiteReturnDomain R (axisFamilyReturnDomain B k t₀ E) n) ∧
        Measurable (finiteReturnJacobian R j n) ∧
        (∀ z ∈ finiteReturnDomain R (axisFamilyReturnDomain B k t₀ E) n,
          1 ≤ finiteReturnJacobian R j n z ∧ finiteReturnJacobian R j n z < ∞ ∧
            (0 < n → 1 < finiteReturnJacobian R j n z)) ∧
        (∀ z ∈ axisFamilySection E,
          z ∈ finiteReturnDomain R (axisFamilyReturnDomain B k t₀ E) n →
          t₀ ≤ cumulativeReturnTime R τ t₀ n z ∧
          axisFamilyChart B k (R^[n] z) = normalizedMaxCurve (axisFamilyChart B k z) t₀
            (cumulativeReturnTime R τ t₀ n z)) ∧
        ∀ S, MeasurableSet S → S ⊆ finiteReturnDomain R (axisFamilyReturnDomain B k t₀ E) n →
          MeasurableSet ((R^[n]) '' S) ∧
          axisFamilyMeasure k ((R^[n]) '' S) = ∫⁻ z in S, finiteReturnJacobian R j n z ∂axisFamilyMeasure k ∧
          (axisFamilyMeasure k ((R^[n]) '' S) = 0 ↔ axisFamilyMeasure k S = 0) ∧
          ∀ g : ι × SectionCoordinates → ℝ≥0∞, Measurable g →
            (∫⁻ w in (R^[n]) '' S, g w ∂axisFamilyMeasure k) =
              ∫⁻ z in S, finiteReturnJacobian R j n z * g (R^[n] z) ∂axisFamilyMeasure k := by
  obtain ⟨R, j, hR, hj, hinj, hfirst, hexpand, hchange⟩ :=
    exists_axisFamily_firstReturn B (t₀ := t₀) hk hε hbound hE hcharts
  obtain ⟨τ, hτ, hleast⟩ := exists_measurable_axisFamily_returnTime B (t₀ := t₀) hk hε hbound hE
  have hstate : ∀ z ∈ axisFamilyReturnDomain B k t₀ E,
      axisFamilyChart B k (R z) = normalizedMaxCurve (axisFamilyChart B k z) t₀ (τ z) := by
    intro z hz
    apply axisFamily_firstReturn_eq_at_returnTime _ hleast hz
    intro w hw
    obtain ⟨t, ht, heq, _⟩ := hfirst w hw
    exact ⟨t, ht, heq⟩
  have hge := fun z hz => (hexpand z hz).1.le
  refine ⟨R, j, τ, hR, hj, hτ, ?_, ?_⟩
  · intro z hz
    exact ⟨hleast z hz, hstate z hz, (hfirst z hz).choose_spec.2.2⟩
  · intro n
    refine ⟨measurableSet_finiteReturnDomain hR (measurableSet_axisFamilyReturnDomain B hk hE) n,
      injOn_finiteReturnIterate hinj n, measurable_finiteReturnJacobian hR hj n, ?_, ?_, ?_⟩
    · intro z hz
      exact ⟨one_le_finiteReturnJacobian hge hz,
        finiteReturnJacobian_lt_top (fun w hw => (hexpand w hw).2) hz,
        fun hn => one_lt_finiteReturnJacobian (fun w hw => (hexpand w hw).1) hn hz⟩
    · intro z hz hvalid
      exact axisFamily_return_iterate_state hk hleast hstate
        (axisFamilySection_chart_of_shear hε hbound hz) n hvalid
    · intro S hS hSD
      have H := measure_image_finiteReturnIterate hR hj hchange n S hS hSD
      exact ⟨H.1, H.2, finiteReturn_image_null_iff hR hj hge hchange n hS hSD,
        fun g hg => setLIntegral_finiteReturnIterate hR hj hg hchange n hS hSD⟩

end BianchiIX
