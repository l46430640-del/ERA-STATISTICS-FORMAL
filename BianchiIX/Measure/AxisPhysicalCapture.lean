import BianchiIX.Measure.AxisReturnRecurrence
import BianchiIX.Measure.AxisReturnCapture

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal

def axisFamilyInfiniteReturns {ι : Type*} (B : ι → NormalizedSymmetry) (k : ι → ℝ) (t₀ : ℝ)
    (E : ι → Set SectionCoordinates) : Set (ι × SectionCoordinates) :=
  {z | z ∈ axisFamilySection E ∧ (axisFamilyReturnTimes B k t₀ E z).Infinite}

theorem measurableSet_axisFamilyInfiniteReturns {ι : Type*} [Finite ι] [Encodable ι] [Nonempty ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι] (B : ι → NormalizedSymmetry)
    {k ε : ι → ℝ} {t₀ : ℝ} {E : ι → Set SectionCoordinates}
    (hk : ∀ i, 0 < k i) (hε : ∀ i, 0 < ε i)
    (hbound : ∀ i, ∀ y ∈ E i, mainWallChart (k i) y 0 ≤ -ε i)
    (hE : ∀ i, MeasurableSet (E i)) (hcharts : InjOn (axisFamilyChart B k) (axisFamilySection E)) :
    MeasurableSet (axisFamilyInfiniteReturns B k t₀ E) := by
  obtain ⟨R, _, hR, _, _, hfirst, _, _⟩ := exists_axisFamily_firstReturn B (t₀ := t₀) hk hε hbound hE hcharts
  obtain ⟨τ, _, hτ⟩ := exists_measurable_axisFamily_returnTime B (t₀ := t₀) hk hε hbound hE
  have hRtime := fun z hz => axisFamily_firstReturn_eq_at_returnTime
    (fun w hw => let ⟨t, ht, hstate, _⟩ := hfirst w hw; ⟨t, ht, hstate⟩) hτ (z := z) hz
  have htarget : MapsTo R (axisFamilyReturnDomain B k t₀ E) (axisFamilySection E) := by
    intro z hz
    obtain ⟨_, _, _, htarget⟩ := hfirst z hz
    exact htarget
  have hD := measurableSet_axisFamilyReturnDomain B (t₀ := t₀) hk hE
  have hall : MeasurableSet {z | ∀ n : ℕ, R^[n] z ∈ axisFamilyReturnDomain B k t₀ E} := by
    simp only [ofPred_forall]
    exact MeasurableSet.iInter (fun n => hD.preimage (hR.iterate n))
  convert! hall using 1
  ext z
  constructor
  · intro hz
    exact (axisFamily_return_iterates_iff_infinite_hits hk hε hbound hτ hRtime htarget hz.1).mpr hz.2
  · intro hz
    have hzE : z ∈ axisFamilySection E := by
      change z.2 ∈ E z.1
      simpa using (hz 0).1
    exact ⟨hzE, (axisFamily_return_iterates_iff_infinite_hits hk hε hbound hτ hRtime htarget hzE).mp hz⟩

/-- Capture expressed solely by intersections of the original flow with the physical section family. -/
theorem ae_axisFamily_physical_capture {ι : Type*} [Finite ι] [Encodable ι] [Nonempty ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι] (B : ι → NormalizedSymmetry)
    {k ε : ι → ℝ} {t₀ : ℝ} {E : ι → Set SectionCoordinates} {F : Set (ι × SectionCoordinates)}
    (hk : ∀ i, 0 < k i) (hε : ∀ i, 0 < ε i)
    (hbound : ∀ i, ∀ y ∈ E i, mainWallChart (k i) y 0 ≤ -ε i)
    (hE : ∀ i, MeasurableSet (E i)) (hcharts : InjOn (axisFamilyChart B k) (axisFamilySection E))
    (hF : MeasurableSet F) (hfinite : axisFamilyMeasure k F ≠ ∞) :
    ∀ᵐ z ∂axisFamilyMeasure k, z ∈ axisFamilyInfiniteReturns B k t₀ E →
      ∃ t ≥ t₀, ∃ w ∈ axisFamilySection E \ F,
        axisFamilyChart B k w = normalizedMaxCurve (axisFamilyChart B k z) t₀ t := by
  obtain ⟨R, _, _, hfirst, hcapture⟩ := exists_axisFamily_firstReturn_capture B (t₀ := t₀) hk hε hbound hE hcharts
  obtain ⟨τ, _, hτ⟩ := exists_measurable_axisFamily_returnTime B (t₀ := t₀) hk hε hbound hE
  have hRtime := fun z hz => axisFamily_firstReturn_eq_at_returnTime
    (fun w hw => let ⟨t, ht, hstate, _⟩ := hfirst w hw; ⟨t, ht, hstate⟩) hτ (z := z) hz
  have htarget : MapsTo R (axisFamilyReturnDomain B k t₀ E) (axisFamilySection E) := by
    intro z hz
    obtain ⟨_, _, _, htarget⟩ := hfirst z hz
    exact htarget
  filter_upwards [(hcapture F hF hfinite).2] with z hz hrec
  have hvalid := (axisFamily_return_iterates_iff_infinite_hits hk hε hbound hτ hRtime htarget hrec.1).mpr hrec.2
  obtain ⟨n, hn⟩ := hz hvalid
  have hzchart := axisFamilySection_chart_of_shear hε hbound hrec.1
  obtain ⟨hle, hstate⟩ := axisFamily_return_iterate_state hk hτ hRtime hzchart n (fun i _ => hvalid i)
  exact ⟨cumulativeReturnTime R τ t₀ n z, hle, R^[n] z, ⟨(hvalid n).1, hn⟩, hstate⟩

theorem ae_smallAxis_physical_capture {h t₀ : ℝ} {E : Fin 3 → Set SectionCoordinates}
    {F : Set (Fin 3 × SectionCoordinates)} (hh : 0 < h) (hh1 : h ≤ 1 / 8)
    (hE : ∀ i, MeasurableSet (E i))
    (hsmall : ∀ i, ∀ y ∈ E i, y ∈ mainWallChartDomain h ∧ |y 0| ≤ 1 / 8 ∧
      Real.exp (-y 1) ≤ h / 8 ∧ Real.exp (-y 2) ≤ h / 8)
    (hF : MeasurableSet F) (hfinite : axisFamilyMeasure (fun _ : Fin 3 => h) F ≠ ∞) :
    ∀ᵐ z ∂axisFamilyMeasure (fun _ : Fin 3 => h),
      z ∈ axisFamilyInfiniteReturns primaryAxisFrame (fun _ => h) t₀ E →
        ∃ t ≥ t₀, ∃ w ∈ axisFamilySection E \ F,
          axisFamilyChart primaryAxisFrame (fun _ => h) w =
            normalizedMaxCurve (axisFamilyChart primaryAxisFrame (fun _ => h) z) t₀ t := by
  have hbound (i : Fin 3) (y : SectionCoordinates) (hy : y ∈ E i) : mainWallChart h y 0 ≤ -(15 / 16) :=
    mainWall_small_target_shear hh hh1 (hsmall i y hy).1 (hsmall i y hy).2.1
      (hsmall i y hy).2.2.1 (hsmall i y hy).2.2.2
  have hdom (i : Fin 3) : E i ⊆ dominantWallChartDomain h := fun y hy =>
    mem_dominantWallChartDomain_of_small hh (hsmall i y hy).1
      (hsmall i y hy).2.2.1 (hsmall i y hy).2.2.2
  exact ae_axisFamily_physical_capture primaryAxisFrame (fun _ => hh)
    (fun _ => by norm_num : ∀ _ : Fin 3, (0 : ℝ) < 15 / 16) hbound hE (primaryAxisChart_injOn hdom) hF hfinite

end BianchiIX
