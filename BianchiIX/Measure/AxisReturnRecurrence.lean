import BianchiIX.Measure.AxisReturnOrbits

noncomputable section

namespace BianchiIX

open Set Filter

variable {ι : Type*} {B : ι → NormalizedSymmetry} {k : ι → ℝ} {t₀ : ℝ}
  {E : ι → Set SectionCoordinates} {R : ι × SectionCoordinates → ι × SectionCoordinates}
  {τ : ι × SectionCoordinates → ℝ}

/-- The coordinate definition agrees exactly with positive-time intersections of the physical union. -/
theorem axisFamily_returnTimes_eq_physical_hits (hk : ∀ i, 0 < k i)
    (hchart : ∀ i, E i ⊆ mainWallChartDomain (k i)) (z : ι × SectionCoordinates) :
    axisFamilyReturnTimes B k t₀ E z =
      {t | t₀ < t ∧ z.2 ∈ mainWallChartDomain (k z.1) ∧ ∃ w ∈ axisFamilySection E,
        axisFamilyChart B k w = normalizedMaxCurve (axisFamilyChart B k z) t₀ t} := by
  ext t
  constructor
  · rintro ⟨ht, i, hrel, hE⟩
    refine ⟨ht, hrel.1,
      (i, axisWallCoordinates (B i) (normalizedMaxCurve (axisWallChart (B z.1) (k z.1) z.2) t₀ t)), hE, ?_⟩
    convert! axisWallArrivalRelation_chart (B z.1) (B i) (hk z.1) hrel using 1
  · rintro ⟨ht, hz, w, hw, hstate⟩
    have H : axisWallChart (B w.1) (k w.1) w.2 =
        normalizedMaxCurve (axisWallChart (B z.1) (k z.1) z.2) t₀ t := by convert! hstate using 1
    refine ⟨ht, w.1, ⟨hz, ?_, ?_, ?_⟩, ?_⟩
    · exact normalizedMaxDomain_contains_Ici (axisWallChart_positive (B z.1) (hk z.1) z.2)
        (axisWallChart_constraint (B z.1) hz) t₀ ht.le
    · rw [← H, axisWallChart, ContinuousLinearEquiv.apply_symm_apply]
      rfl
    · rw [← H, axisWallChart, ContinuousLinearEquiv.apply_symm_apply]
      exact mainWallChart_negative (hchart w.1 hw)
    · rw [← H, axisWallCoordinates_chart]
      exact hw

theorem axisFamily_infinite_hittingTimes_iff_unbounded [Finite ι] {ε : ι → ℝ}
    (hk : ∀ i, 0 < k i) (hε : ∀ i, 0 < ε i)
    (hbound : ∀ i, ∀ y ∈ E i, mainWallChart (k i) y 0 ≤ -ε i)
    {z : ι × SectionCoordinates} (hz : z.2 ∈ mainWallChartDomain (k z.1)) :
    (axisFamilyReturnTimes B k t₀ E z).Infinite ↔ ¬ BddAbove (axisFamilyReturnTimes B k t₀ E z) := by
  constructor
  · intro hinfinite hbounded
    obtain ⟨T, hT⟩ := hbounded
    have hfinite := finite_axisFamilyHittingTimes (B z.1) B (t₀ := t₀) (T := T) (I := Ioi t₀)
      (hk z.1) hk hε hz hbound
    exact hinfinite (hfinite.subset (fun t ht => ⟨ht, le_of_lt ht.1, hT ht⟩))
  · exact infinite_of_not_bddAbove

/-- Arbitrarily late physical hits keep every iterate inside the genuine return domain. -/
theorem axisFamily_return_iterates_of_unbounded_hits (hk : ∀ i, 0 < k i)
    (hchart : ∀ i, E i ⊆ mainWallChartDomain (k i))
    (hτ : ∀ z ∈ axisFamilyReturnDomain B k t₀ E, IsLeast (axisFamilyReturnTimes B k t₀ E z) (τ z))
    (hR : ∀ z ∈ axisFamilyReturnDomain B k t₀ E,
      axisFamilyChart B k (R z) = normalizedMaxCurve (axisFamilyChart B k z) t₀ (τ z))
    (htarget : MapsTo R (axisFamilyReturnDomain B k t₀ E) (axisFamilySection E))
    {z : ι × SectionCoordinates} (hzE : z ∈ axisFamilySection E)
    (hunbounded : ¬ BddAbove (axisFamilyReturnTimes B k t₀ E z)) :
    ∀ n, R^[n] z ∈ axisFamilyReturnDomain B k t₀ E := by
  have hz := hchart z.1 hzE
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hstate := axisFamily_return_iterate_state hk hτ hR hz n ih
    have hmember : R^[n] z ∈ axisFamilySection E := by
      cases n with
      | zero => simpa using hzE
      | succ m =>
        rw [Function.iterate_succ_apply']
        exact htarget (ih m (Nat.lt_succ_self m))
    have hw := hchart (R^[n] z).1 hmember
    obtain ⟨t, ht, hnt⟩ := not_bddAbove_iff.mp hunbounded (cumulativeReturnTime R τ t₀ n z)
    have hhit := (axisFamily_hittingTimes_after_time hk hz hw hstate.1 hstate.2 hnt).mp ht
    exact ⟨hmember, ⟨t₀ + (t - cumulativeReturnTime R τ t₀ n z), hhit⟩⟩

theorem axisFamily_return_iterates_iff_infinite_hits [Finite ι] (hk : ∀ i, 0 < k i) {ε : ι → ℝ}
    (hε : ∀ i, 0 < ε i) (hbound : ∀ i, ∀ y ∈ E i, mainWallChart (k i) y 0 ≤ -ε i)
    (hτ : ∀ z ∈ axisFamilyReturnDomain B k t₀ E, IsLeast (axisFamilyReturnTimes B k t₀ E z) (τ z))
    (hR : ∀ z ∈ axisFamilyReturnDomain B k t₀ E,
      axisFamilyChart B k (R z) = normalizedMaxCurve (axisFamilyChart B k z) t₀ (τ z))
    (htarget : MapsTo R (axisFamilyReturnDomain B k t₀ E) (axisFamilySection E))
    {z : ι × SectionCoordinates} (hzE : z ∈ axisFamilySection E) :
    (∀ n, R^[n] z ∈ axisFamilyReturnDomain B k t₀ E) ↔ (axisFamilyReturnTimes B k t₀ E z).Infinite := by
  constructor
  · intro hvalid
    have hm := axisFamily_return_times_strictMono hτ hvalid
    apply (infinite_range_of_injective (f := fun n => cumulativeReturnTime R τ t₀ (n + 1) z)
      (fun _ _ heq => Nat.add_right_cancel (hm.injective heq))).mono
    rintro _ ⟨n, rfl⟩
    exact axisFamily_return_time_mem hk hτ hR hvalid (Nat.zero_lt_succ n)
  · intro hinfinite
    have hchart (i : ι) : E i ⊆ mainWallChartDomain (k i) := fun _ hy =>
      axisFamilySection_chart_of_shear hε hbound (z := (i, _)) hy
    exact axisFamily_return_iterates_of_unbounded_hits hk hchart hτ hR htarget hzE
      ((axisFamily_infinite_hittingTimes_iff_unbounded hk hε hbound (hchart z.1 hzE)).mp hinfinite)

/-- The return times enumerate all positive physical hits of the entire section family. -/
theorem axisFamily_hittingTimes_eq_returnTime_range [Finite ι] (hk : ∀ i, 0 < k i) {ε : ι → ℝ}
    (hε : ∀ i, 0 < ε i) (hbound : ∀ i, ∀ y ∈ E i, mainWallChart (k i) y 0 ≤ -ε i)
    (hτ : ∀ z ∈ axisFamilyReturnDomain B k t₀ E, IsLeast (axisFamilyReturnTimes B k t₀ E z) (τ z))
    (hR : ∀ z ∈ axisFamilyReturnDomain B k t₀ E,
      axisFamilyChart B k (R z) = normalizedMaxCurve (axisFamilyChart B k z) t₀ (τ z))
    {z : ι × SectionCoordinates} (hvalid : ∀ n, R^[n] z ∈ axisFamilyReturnDomain B k t₀ E) :
    axisFamilyReturnTimes B k t₀ E z = range (fun n => cumulativeReturnTime R τ t₀ (n + 1) z) := by
  ext t
  constructor
  · intro ht
    have hlim := axisFamily_return_times_tendsto hk hε hbound hτ hR hvalid
    have hex : ∃ n, t ≤ cumulativeReturnTime R τ t₀ n z :=
      (hlim.eventually (eventually_ge_atTop t)).exists
    have hm := Nat.find_spec hex
    have hmpos : Nat.find hex ≠ 0 := by
      intro hz
      rw [hz, cumulativeReturnTime_zero] at hm
      exact (not_le_of_gt ht.1) hm
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hmpos
    have hprev : cumulativeReturnTime R τ t₀ n z < t :=
      lt_of_not_ge (Nat.find_min hex (by omega : n < Nat.find hex))
    have hnext := (axisFamily_return_next_time_isLeast hk hτ hR hvalid n).2 ⟨ht, hprev⟩
    refine ⟨n, le_antisymm hnext ?_⟩
    simpa [hn] using hm
  · rintro ⟨n, rfl⟩
    exact axisFamily_return_time_mem hk hτ hR hvalid (Nat.zero_lt_succ n)

end BianchiIX
