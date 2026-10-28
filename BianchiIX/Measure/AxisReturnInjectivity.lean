import BianchiIX.Dynamics.AxisFamilySections
import BianchiIX.Dynamics.FlowInjectivity

noncomputable section

namespace BianchiIX

open Set MeasureTheory

def axisFamilyReturnTimes {ι : Type*} (B : ι → NormalizedSymmetry) (k : ι → ℝ) (t₀ : ℝ)
    (E : ι → Set SectionCoordinates) (z : ι × SectionCoordinates) : Set ℝ :=
  axisFamilyHittingTimes (B z.1) B (k z.1) k t₀ E (Ioi t₀) z.2

def axisFamilyReturnDomain {ι : Type*} (B : ι → NormalizedSymmetry) (k : ι → ℝ) (t₀ : ℝ)
    (E : ι → Set SectionCoordinates) : Set (ι × SectionCoordinates) :=
  {z | z.2 ∈ E z.1 ∧ (axisFamilyReturnTimes B k t₀ E z).Nonempty}

theorem measurableSet_axisFamilyReturnDomain {ι : Type*} [Countable ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] (B : ι → NormalizedSymmetry) {k : ι → ℝ} {t₀ : ℝ}
    {E : ι → Set SectionCoordinates} (hk : ∀ i, 0 < k i) (hE : ∀ i, MeasurableSet (E i)) :
    MeasurableSet (axisFamilyReturnDomain B k t₀ E) := by
  have heq : axisFamilyReturnDomain B k t₀ E = ⋃ i,
      {i} ×ˢ (E i ∩ axisFamilyHittingDomain (B i) B (k i) k t₀ E (Ioi t₀)) := by
    ext z
    simp [axisFamilyReturnDomain, axisFamilyReturnTimes, axisFamilyHittingDomain]
  rw [heq]
  exact MeasurableSet.iUnion (fun i => (measurableSet_singleton i).prod
    ((hE i).inter (measurableSet_axisFamilyHittingDomain (B i) B (hk i) hk hE measurableSet_Ioi)))

/-- Earliest returns cannot merge; injective physical charts remove any ambiguity of axis labels. -/
theorem axisFamily_firstReturn_pair_injective {ι : Type*} (B : ι → NormalizedSymmetry)
    {k : ι → ℝ} {t₀ s t : ℝ} {E : ι → Set SectionCoordinates} {x y : ι × SectionCoordinates}
    (hk : ∀ i, 0 < k i) (hcharts : InjOn (axisFamilyChart B k) (axisFamilySection E))
    (hx : x ∈ axisFamilySection E) (hy : y ∈ axisFamilySection E)
    (hs : IsLeast (axisFamilyReturnTimes B k t₀ E x) s)
    (ht : IsLeast (axisFamilyReturnTimes B k t₀ E y) t)
    (heq : normalizedMaxCurve (axisFamilyChart B k x) t₀ s =
      normalizedMaxCurve (axisFamilyChart B k y) t₀ t) : x = y := by
  have hnot {u v : ι × SectionCoordinates} {a b : ℝ} (hu : u ∈ axisFamilySection E)
      (ha : IsLeast (axisFamilyReturnTimes B k t₀ E u) a)
      (hb : IsLeast (axisFamilyReturnTimes B k t₀ E v) b) (hab : a < b)
      (H : normalizedMaxCurve (axisFamilyChart B k u) t₀ a =
        normalizedMaxCurve (axisFamilyChart B k v) t₀ b) : False := by
    have huc := axisFamilyHittingTimes_source ha.1
    have hvc := axisFamilyHittingTimes_source hb.1
    have hz := normalizedMaxCurve_eq_at_time_difference
      (axisWallChart_positive (B u.1) (hk u.1) u.2) (axisWallChart_constraint (B u.1) huc)
      (axisWallChart_positive (B v.1) (hk v.1) v.2) (axisWallChart_constraint (B v.1) hvc)
      ha.1.1.le hab.le H
    have htime : t₀ + (b - a) ∈ axisFamilyReturnTimes B k t₀ E v := by
      refine ⟨by change t₀ < t₀ + (b - a); linarith, u.1, ⟨hvc, ?_, ?_, ?_⟩, ?_⟩
      · exact normalizedMaxDomain_contains_Ici (axisWallChart_positive (B v.1) (hk v.1) v.2)
          (axisWallChart_constraint (B v.1) hvc) t₀ (show t₀ ≤ t₀ + (b - a) by linarith)
      · rw [hz, axisWallChart, ContinuousLinearEquiv.apply_symm_apply]
        rfl
      · rw [hz, axisWallChart, ContinuousLinearEquiv.apply_symm_apply]
        exact mainWallChart_negative huc
      · rw [hz, axisWallCoordinates_chart]
        exact hu
    have hmin := hb.2 htime
    have ha0 := ha.1.1
    change t₀ < a at ha0
    linarith
  have hst : s = t := by
    rcases lt_trichotomy s t with hlt | he | hgt
    · exact (hnot hx hs ht hlt heq).elim
    · exact he
    · exact (hnot hy ht hs hgt heq.symm).elim
  have hs0 : t₀ < s := hs.1.1
  apply hcharts hx hy
  apply normalizedMaxCurve_injOn t₀ s
  · exact normalizedMaxDomain_contains_Ici (axisWallChart_positive (B x.1) (hk x.1) x.2)
      (axisWallChart_constraint (B x.1) (axisFamilyHittingTimes_source hs.1)) t₀ hs0.le
  · exact normalizedMaxDomain_contains_Ici (axisWallChart_positive (B y.1) (hk y.1) y.2)
      (axisWallChart_constraint (B y.1) (axisFamilyHittingTimes_source ht.1)) t₀ hs0.le
  · simpa [hst] using heq

theorem axisFamily_firstReturn_injOn {ι : Type*} (B : ι → NormalizedSymmetry)
    {k : ι → ℝ} {t₀ : ℝ} {E : ι → Set SectionCoordinates}
    {R : ι × SectionCoordinates → ι × SectionCoordinates}
    (hk : ∀ i, 0 < k i) (hcharts : InjOn (axisFamilyChart B k) (axisFamilySection E))
    (hfirst : ∀ z ∈ axisFamilyReturnDomain B k t₀ E, ∃ t,
      IsLeast (axisFamilyReturnTimes B k t₀ E z) t ∧
      axisFamilyChart B k (R z) = normalizedMaxCurve (axisFamilyChart B k z) t₀ t) :
    InjOn R (axisFamilyReturnDomain B k t₀ E) := by
  intro x hx y hy heq
  obtain ⟨s, hs, hRx⟩ := hfirst x hx
  obtain ⟨t, ht, hRy⟩ := hfirst y hy
  exact axisFamily_firstReturn_pair_injective B hk hcharts hx.1 hy.1 hs ht
    (hRx.symm.trans ((congrArg (axisFamilyChart B k) heq).trans hRy))

end BianchiIX
