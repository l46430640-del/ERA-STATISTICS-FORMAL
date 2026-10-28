import BianchiIX.Measure.AxisReturnTime

noncomputable section

namespace BianchiIX

open Set MeasureTheory Filter

variable {ι : Type*} {B : ι → NormalizedSymmetry} {k : ι → ℝ} {t₀ : ℝ}
  {E : ι → Set SectionCoordinates} {R : ι × SectionCoordinates → ι × SectionCoordinates}
  {τ : ι × SectionCoordinates → ℝ}

/-- Every finite legal cross-axis return string follows one original Einstein orbit. -/
theorem axisFamily_return_iterate_state (hk : ∀ i, 0 < k i)
    (hτ : ∀ z ∈ axisFamilyReturnDomain B k t₀ E, IsLeast (axisFamilyReturnTimes B k t₀ E z) (τ z))
    (hR : ∀ z ∈ axisFamilyReturnDomain B k t₀ E,
      axisFamilyChart B k (R z) = normalizedMaxCurve (axisFamilyChart B k z) t₀ (τ z))
    {z : ι × SectionCoordinates} (hz : z.2 ∈ mainWallChartDomain (k z.1)) (n : ℕ)
    (hvalid : ∀ i < n, R^[i] z ∈ axisFamilyReturnDomain B k t₀ E) :
    t₀ ≤ cumulativeReturnTime R τ t₀ n z ∧
      axisFamilyChart B k (R^[n] z) = normalizedMaxCurve (axisFamilyChart B k z) t₀
        (cumulativeReturnTime R τ t₀ n z) := by
  induction n with
  | zero => simp [normalizedMaxCurve_initial]
  | succ n ih =>
    obtain ⟨hle, hstate⟩ := ih (fun i hi => hvalid i (Nat.lt_trans hi (Nat.lt_succ_self n)))
    have hn := hvalid n (Nat.lt_succ_self n)
    have hpos : t₀ < τ (R^[n] z) := (hτ _ hn).1.1
    have hnext : t₀ ≤ cumulativeReturnTime R τ t₀ (n + 1) z := by
      rw [cumulativeReturnTime_succ]
      linarith
    refine ⟨hnext, ?_⟩
    have hstart : t₀ + (cumulativeReturnTime R τ t₀ n z - t₀) ∈
        normalizedMaxDomain (axisFamilyChart B k z) t₀ := by
      convert! normalizedMaxDomain_contains_Ici (axisWallChart_positive (B z.1) (hk z.1) z.2)
        (axisWallChart_constraint (B z.1) hz) t₀
        (show t₀ ≤ t₀ + (cumulativeReturnTime R τ t₀ n z - t₀) by linarith) using 1
    have hend : τ (R^[n] z) + (cumulativeReturnTime R τ t₀ n z - t₀) ∈
        normalizedMaxDomain (axisFamilyChart B k z) t₀ := by
      convert! normalizedMaxDomain_contains_Ici (axisWallChart_positive (B z.1) (hk z.1) z.2)
        (axisWallChart_constraint (B z.1) hz) t₀
        (show t₀ ≤ τ (R^[n] z) + (cumulativeReturnTime R τ t₀ n z - t₀) by linarith) using 1
    have H := normalizedMaxCurve_shift hstart hend
    rw [show t₀ + (cumulativeReturnTime R τ t₀ n z - t₀) =
      cumulativeReturnTime R τ t₀ n z by ring, ← hstate] at H
    rw [Function.iterate_succ_apply', hR _ hn, H, cumulativeReturnTime_succ]
    congr 1
    ring

theorem axisFamily_return_times_strictMono
    (hτ : ∀ z ∈ axisFamilyReturnDomain B k t₀ E, IsLeast (axisFamilyReturnTimes B k t₀ E z) (τ z))
    {z : ι × SectionCoordinates} (hvalid : ∀ n, R^[n] z ∈ axisFamilyReturnDomain B k t₀ E) :
    StrictMono (fun n => cumulativeReturnTime R τ t₀ n z) := by
  apply strictMono_nat_of_lt_succ
  intro n
  have hpos : t₀ < τ (R^[n] z) := (hτ _ (hvalid n)).1.1
  rw [cumulativeReturnTime_succ]
  linarith

theorem axisFamily_return_time_mem (hk : ∀ i, 0 < k i)
    (hτ : ∀ z ∈ axisFamilyReturnDomain B k t₀ E, IsLeast (axisFamilyReturnTimes B k t₀ E z) (τ z))
    (hR : ∀ z ∈ axisFamilyReturnDomain B k t₀ E,
      axisFamilyChart B k (R z) = normalizedMaxCurve (axisFamilyChart B k z) t₀ (τ z))
    {z : ι × SectionCoordinates} (hvalid : ∀ n, R^[n] z ∈ axisFamilyReturnDomain B k t₀ E)
    {n : ℕ} (hn : 0 < n) : cumulativeReturnTime R τ t₀ n z ∈ axisFamilyReturnTimes B k t₀ E z := by
  have hz : z.2 ∈ mainWallChartDomain (k z.1) := by
    simpa using axisFamilyHittingTimes_source (hτ _ (hvalid 0)).1
  have hpos : t₀ < cumulativeReturnTime R τ t₀ n z := by
    simpa using axisFamily_return_times_strictMono hτ hvalid hn
  have hstate := (axisFamily_return_iterate_state hk hτ hR hz n (fun i _ => hvalid i)).2
  have hstate' : axisWallChart (B (R^[n] z).1) (k (R^[n] z).1) (R^[n] z).2 =
      normalizedMaxCurve (axisWallChart (B z.1) (k z.1) z.2) t₀ (cumulativeReturnTime R τ t₀ n z) := by
    convert! hstate using 1
  have hnchart := axisFamilyHittingTimes_source (hτ _ (hvalid n)).1
  refine ⟨hpos, (R^[n] z).1, ⟨hz, ?_, ?_, ?_⟩, ?_⟩
  · exact normalizedMaxDomain_contains_Ici (axisWallChart_positive (B z.1) (hk z.1) z.2)
      (axisWallChart_constraint (B z.1) hz) t₀ hpos.le
  · rw [← hstate', axisWallChart, ContinuousLinearEquiv.apply_symm_apply]
    rfl
  · rw [← hstate', axisWallChart, ContinuousLinearEquiv.apply_symm_apply]
    exact mainWallChart_negative hnchart
  · rw [← hstate', axisWallCoordinates_chart]
    exact (hvalid n).1

theorem axisFamily_return_times_tendsto [Finite ι] (hk : ∀ i, 0 < k i) {ε : ι → ℝ}
    (hε : ∀ i, 0 < ε i) (hbound : ∀ i, ∀ y ∈ E i, mainWallChart (k i) y 0 ≤ -ε i)
    (hτ : ∀ z ∈ axisFamilyReturnDomain B k t₀ E, IsLeast (axisFamilyReturnTimes B k t₀ E z) (τ z))
    (hR : ∀ z ∈ axisFamilyReturnDomain B k t₀ E,
      axisFamilyChart B k (R z) = normalizedMaxCurve (axisFamilyChart B k z) t₀ (τ z))
    {z : ι × SectionCoordinates} (hvalid : ∀ n, R^[n] z ∈ axisFamilyReturnDomain B k t₀ E) :
    Tendsto (fun n => cumulativeReturnTime R τ t₀ n z) atTop atTop := by
  have hm := axisFamily_return_times_strictMono hτ hvalid
  apply tendsto_atTop_atTop_of_monotone' hm.monotone
  rintro ⟨T, hT⟩
  have hz : z.2 ∈ mainWallChartDomain (k z.1) := by
    simpa using axisFamilyHittingTimes_source (hτ _ (hvalid 0)).1
  have hfinite := finite_axisFamilyHittingTimes (B z.1) B (t₀ := t₀) (T := T) (I := Ioi t₀)
    (hk z.1) hk hε hz hbound
  have hsub : range (fun n => cumulativeReturnTime R τ t₀ (n + 1) z) ⊆
      axisFamilyReturnTimes B k t₀ E z ∩ Icc t₀ T := by
    rintro _ ⟨n, rfl⟩
    have hhit := axisFamily_return_time_mem hk hτ hR hvalid (Nat.zero_lt_succ n)
    exact ⟨hhit, le_of_lt hhit.1, hT (mem_range_self (n + 1))⟩
  have hinfinite := infinite_range_of_injective (f := fun n => cumulativeReturnTime R τ t₀ (n + 1) z)
    (fun _ _ heq => Nat.add_right_cancel (hm.injective heq))
  exact hinfinite (hfinite.subset hsub)

theorem axisFamily_hittingTimes_after_time (hk : ∀ i, 0 < k i) {z w : ι × SectionCoordinates} {s t : ℝ}
    (hz : z.2 ∈ mainWallChartDomain (k z.1)) (hw : w.2 ∈ mainWallChartDomain (k w.1)) (hs : t₀ ≤ s)
    (hstate : axisFamilyChart B k w = normalizedMaxCurve (axisFamilyChart B k z) t₀ s) (ht : s < t) :
    t ∈ axisFamilyReturnTimes B k t₀ E z ↔ t₀ + (t - s) ∈ axisFamilyReturnTimes B k t₀ E w := by
  have hu : t₀ + (s - t₀) ∈ normalizedMaxDomain (axisFamilyChart B k z) t₀ := by
    convert! normalizedMaxDomain_contains_Ici (axisWallChart_positive (B z.1) (hk z.1) z.2)
      (axisWallChart_constraint (B z.1) hz) t₀ (show t₀ ≤ t₀ + (s - t₀) by linarith) using 1
  have hv : (t₀ + (t - s)) + (s - t₀) ∈ normalizedMaxDomain (axisFamilyChart B k z) t₀ := by
    convert! normalizedMaxDomain_contains_Ici (axisWallChart_positive (B z.1) (hk z.1) z.2)
      (axisWallChart_constraint (B z.1) hz) t₀ (show t₀ ≤ (t₀ + (t - s)) + (s - t₀) by linarith) using 1
  have H := normalizedMaxCurve_shift hu hv
  rw [show t₀ + (s - t₀) = s by ring, ← hstate,
    show (t₀ + (t - s)) + (s - t₀) = t by ring] at H
  have H' : normalizedMaxCurve (axisWallChart (B w.1) (k w.1) w.2) t₀ (t₀ + (t - s)) =
      normalizedMaxCurve (axisWallChart (B z.1) (k z.1) z.2) t₀ t := by convert! H using 1
  constructor
  · rintro ⟨_, i, hrel, hE⟩
    refine ⟨show t₀ < t₀ + (t - s) by linarith, i, ⟨hw, ?_, ?_, ?_⟩, ?_⟩
    · exact normalizedMaxDomain_contains_Ici (axisWallChart_positive (B w.1) (hk w.1) w.2)
        (axisWallChart_constraint (B w.1) hw) t₀ (show t₀ ≤ t₀ + (t - s) by linarith)
    · rw [H']; exact hrel.2.2.1
    · rw [H']; exact hrel.2.2.2
    · rw [H']; exact hE
  · rintro ⟨_, i, hrel, hE⟩
    refine ⟨hs.trans_lt ht, i, ⟨hz, ?_, ?_, ?_⟩, ?_⟩
    · exact normalizedMaxDomain_contains_Ici (axisWallChart_positive (B z.1) (hk z.1) z.2)
        (axisWallChart_constraint (B z.1) hz) t₀ (hs.trans ht.le)
    · rw [← H']; exact hrel.2.2.1
    · rw [← H']; exact hrel.2.2.2
    · rw [← H']; exact hE

theorem axisFamily_return_next_time_isLeast (hk : ∀ i, 0 < k i)
    (hτ : ∀ z ∈ axisFamilyReturnDomain B k t₀ E, IsLeast (axisFamilyReturnTimes B k t₀ E z) (τ z))
    (hR : ∀ z ∈ axisFamilyReturnDomain B k t₀ E,
      axisFamilyChart B k (R z) = normalizedMaxCurve (axisFamilyChart B k z) t₀ (τ z))
    {z : ι × SectionCoordinates} (hvalid : ∀ n, R^[n] z ∈ axisFamilyReturnDomain B k t₀ E) (n : ℕ) :
    IsLeast (axisFamilyReturnTimes B k t₀ E z ∩ Ioi (cumulativeReturnTime R τ t₀ n z))
      (cumulativeReturnTime R τ t₀ (n + 1) z) := by
  have hz : z.2 ∈ mainWallChartDomain (k z.1) := by
    simpa using axisFamilyHittingTimes_source (hτ _ (hvalid 0)).1
  have hw := axisFamilyHittingTimes_source (hτ _ (hvalid n)).1
  have hstate := axisFamily_return_iterate_state hk hτ hR hz n (fun i _ => hvalid i)
  refine ⟨⟨axisFamily_return_time_mem hk hτ hR hvalid (Nat.zero_lt_succ n),
    axisFamily_return_times_strictMono hτ hvalid (Nat.lt_succ_self n)⟩, ?_⟩
  rintro t ⟨ht, hnt⟩
  have hlocal := (axisFamily_hittingTimes_after_time hk hz hw hstate.1 hstate.2 hnt).mp ht
  have hmin := (hτ _ (hvalid n)).2 hlocal
  rw [cumulativeReturnTime_succ]
  linarith

end BianchiIX
