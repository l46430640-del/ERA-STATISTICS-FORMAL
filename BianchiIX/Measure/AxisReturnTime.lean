import BianchiIX.Measure.AxisReturnMap
import BianchiIX.Measure.MainWallReturnTime

noncomputable section

namespace BianchiIX

open Set MeasureTheory

theorem mainWallChartDomain_of_negative {h : ℝ} {y : SectionCoordinates}
    (hy : mainWallChart h y 0 < 0) : y ∈ mainWallChartDomain h := by
  change -Real.sqrt (mainWallRadicand h y) < 0 at hy
  exact Real.sqrt_pos.mp (by linarith)

theorem axisFamilySection_chart_of_shear {ι : Type*} {k ε : ι → ℝ}
    {E : ι → Set SectionCoordinates} (hε : ∀ i, 0 < ε i)
    (hbound : ∀ i, ∀ y ∈ E i, mainWallChart (k i) y 0 ≤ -ε i)
    {z : ι × SectionCoordinates} (hz : z ∈ axisFamilySection E) : z.2 ∈ mainWallChartDomain (k z.1) :=
  mainWallChartDomain_of_negative ((hbound z.1 z.2 hz).trans_lt (neg_neg_of_pos (hε z.1)))

theorem exists_measurable_axisFamily_returnTime {ι : Type*} [Finite ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι] (B : ι → NormalizedSymmetry)
    {k ε : ι → ℝ} {t₀ : ℝ} {E : ι → Set SectionCoordinates}
    (hk : ∀ i, 0 < k i) (hε : ∀ i, 0 < ε i)
    (hbound : ∀ i, ∀ z ∈ E i, mainWallChart (k i) z 0 ≤ -ε i)
    (hE : ∀ i, MeasurableSet (E i)) :
    ∃ τ : ι × SectionCoordinates → ℝ, Measurable τ ∧
      ∀ z ∈ axisFamilyReturnDomain B k t₀ E, IsLeast (axisFamilyReturnTimes B k t₀ E z) (τ z) := by
  classical
  have hlocal (i : ι) := exists_measurable_axisFamily_firstTime (B i) B (t₀ := t₀)
    (hk i) hk hε (show Ioi t₀ ⊆ Ici t₀ from fun x hx => show t₀ ≤ x from le_of_lt hx)
    hbound hE measurableSet_Ioi
  choose τ hτ hfirst using hlocal
  exact ⟨fun z => τ z.1 z.2, measurable_from_prod_countable_right hτ, fun z hz => hfirst z.1 z.2 hz.2⟩

theorem axisFamily_firstReturn_eq_at_returnTime {ι : Type*} {B : ι → NormalizedSymmetry}
    {k : ι → ℝ} {t₀ : ℝ} {E : ι → Set SectionCoordinates}
    {R : ι × SectionCoordinates → ι × SectionCoordinates} {τ : ι × SectionCoordinates → ℝ}
    (hfirst : ∀ z ∈ axisFamilyReturnDomain B k t₀ E, ∃ t,
      IsLeast (axisFamilyReturnTimes B k t₀ E z) t ∧
      axisFamilyChart B k (R z) = normalizedMaxCurve (axisFamilyChart B k z) t₀ t)
    (hτ : ∀ z ∈ axisFamilyReturnDomain B k t₀ E, IsLeast (axisFamilyReturnTimes B k t₀ E z) (τ z))
    {z : ι × SectionCoordinates} (hz : z ∈ axisFamilyReturnDomain B k t₀ E) :
    axisFamilyChart B k (R z) = normalizedMaxCurve (axisFamilyChart B k z) t₀ (τ z) := by
  obtain ⟨t, ht, heq⟩ := hfirst z hz
  rwa [ht.unique (hτ z hz)] at heq

end BianchiIX
