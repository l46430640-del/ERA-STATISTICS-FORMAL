import BianchiIX.Measure.MainWallReturnTime

noncomputable section

namespace BianchiIX

open Set MeasureTheory Filter

variable {h t₀ : ℝ} {B : Set SectionCoordinates}
  {R : SectionCoordinates → SectionCoordinates} {τ : SectionCoordinates → ℝ}

/-- Every finite string of legal returns lies on one exact Einstein orbit. -/
theorem mainWall_return_iterate_state (hh : 0 < h)
    (hτ : ∀ y ∈ mainWallReturnDomain h t₀ B,
      IsLeast (mainWallHittingTimes h h t₀ B (Ioi t₀) y) (τ y))
    (hR : ∀ y ∈ mainWallReturnDomain h t₀ B,
      R y = mainWallCoordinates (normalizedMaxCurve (mainWallChart h y) t₀ (τ y)))
    {y : SectionCoordinates} (hy : y ∈ mainWallChartDomain h) (n : ℕ)
    (hvalid : ∀ i < n, R^[i] y ∈ mainWallReturnDomain h t₀ B) :
    t₀ ≤ cumulativeReturnTime R τ t₀ n y ∧
      mainWallChart h (R^[n] y) = normalizedMaxCurve (mainWallChart h y) t₀
        (cumulativeReturnTime R τ t₀ n y) := by
  induction n with
  | zero => simp [normalizedMaxCurve_initial]
  | succ n ih =>
    obtain ⟨hle, hstate⟩ := ih (fun i hi => hvalid i (Nat.lt_trans hi (Nat.lt_succ_self n)))
    have hn := hvalid n (Nat.lt_succ_self n)
    have ht := hτ _ hn
    have hpos : t₀ < τ (R^[n] y) := ht.1.1
    have hnext : t₀ ≤ cumulativeReturnTime R τ t₀ (n + 1) y := by
      rw [cumulativeReturnTime_succ]
      linarith
    refine ⟨hnext, ?_⟩
    have heq : mainWallChart h (R (R^[n] y)) =
        normalizedMaxCurve (mainWallChart h (R^[n] y)) t₀ (τ (R^[n] y)) := by
      rw [hR _ hn]
      exact mainWallArrivalRelation_chart hh ht.1.2.1
    have hstart := normalizedMaxDomain_contains_Ici (mainWallChart_positive hh y)
      (mainWallChart_constraint hy) t₀
      (show t₀ ≤ t₀ + (cumulativeReturnTime R τ t₀ n y - t₀) by linarith)
    have hend := normalizedMaxDomain_contains_Ici (mainWallChart_positive hh y)
      (mainWallChart_constraint hy) t₀
      (show t₀ ≤ τ (R^[n] y) + (cumulativeReturnTime R τ t₀ n y - t₀) by linarith)
    have H := normalizedMaxCurve_shift hstart hend
    rw [show t₀ + (cumulativeReturnTime R τ t₀ n y - t₀) =
      cumulativeReturnTime R τ t₀ n y by ring, ← hstate] at H
    rw [Function.iterate_succ_apply', heq, H, cumulativeReturnTime_succ]
    congr 1
    ring

theorem mainWall_return_times_strictMono
    (hτ : ∀ y ∈ mainWallReturnDomain h t₀ B,
      IsLeast (mainWallHittingTimes h h t₀ B (Ioi t₀) y) (τ y))
    {y : SectionCoordinates} (hvalid : ∀ n, R^[n] y ∈ mainWallReturnDomain h t₀ B) :
    StrictMono (fun n => cumulativeReturnTime R τ t₀ n y) := by
  apply strictMono_nat_of_lt_succ
  intro n
  have hpos : t₀ < τ (R^[n] y) := (hτ _ (hvalid n)).1.1
  rw [cumulativeReturnTime_succ]
  linarith

theorem mainWall_return_time_mem (hh : 0 < h)
    (hτ : ∀ y ∈ mainWallReturnDomain h t₀ B,
      IsLeast (mainWallHittingTimes h h t₀ B (Ioi t₀) y) (τ y))
    (hR : ∀ y ∈ mainWallReturnDomain h t₀ B,
      R y = mainWallCoordinates (normalizedMaxCurve (mainWallChart h y) t₀ (τ y)))
    {y : SectionCoordinates} (hvalid : ∀ n, R^[n] y ∈ mainWallReturnDomain h t₀ B)
    {n : ℕ} (hn : 0 < n) :
    cumulativeReturnTime R τ t₀ n y ∈ mainWallHittingTimes h h t₀ B (Ioi t₀) y := by
  have hy : y ∈ mainWallChartDomain h := by simpa using (hτ _ (hvalid 0)).1.2.1.1
  have hpos : t₀ < cumulativeReturnTime R τ t₀ n y := by
    simpa using mainWall_return_times_strictMono hτ hvalid hn
  have hstate := (mainWall_return_iterate_state hh hτ hR hy n (fun i _ => hvalid i)).2
  have hnchart := (hτ _ (hvalid n)).1.2.1.1
  refine ⟨hpos, ⟨hy, ?_, ?_, ?_⟩, ?_⟩
  · exact normalizedMaxDomain_contains_Ici (mainWallChart_positive hh y)
      (mainWallChart_constraint hy) t₀ hpos.le
  · rw [← hstate]
    rfl
  · rw [← hstate]
    exact mainWallChart_negative hnchart
  · rw [← hstate, mainWallCoordinates_chart]
    exact (hvalid n).1

/-- Local finiteness excludes finite-time accumulation without a uniform flight-time lower bound. -/
theorem mainWall_return_times_tendsto (hh : 0 < h) {ε : ℝ} (hε : 0 < ε)
    (hbound : ∀ z ∈ B, mainWallChart h z 0 ≤ -ε)
    (hτ : ∀ y ∈ mainWallReturnDomain h t₀ B,
      IsLeast (mainWallHittingTimes h h t₀ B (Ioi t₀) y) (τ y))
    (hR : ∀ y ∈ mainWallReturnDomain h t₀ B,
      R y = mainWallCoordinates (normalizedMaxCurve (mainWallChart h y) t₀ (τ y)))
    {y : SectionCoordinates} (hvalid : ∀ n, R^[n] y ∈ mainWallReturnDomain h t₀ B) :
    Tendsto (fun n => cumulativeReturnTime R τ t₀ n y) atTop atTop := by
  have hm := mainWall_return_times_strictMono hτ hvalid
  apply tendsto_atTop_atTop_of_monotone' hm.monotone
  rintro ⟨T, hT⟩
  have hy : y ∈ mainWallChartDomain h := by simpa using (hτ _ (hvalid 0)).1.2.1.1
  have hfinite := finite_mainWallHittingTimes (t₀ := t₀) (T := T) (I := Ioi t₀) hh hh hε hy hbound
  have hsub : range (fun n => cumulativeReturnTime R τ t₀ (n + 1) y) ⊆
      mainWallHittingTimes h h t₀ B (Ioi t₀) y ∩ Icc t₀ T := by
    rintro _ ⟨n, rfl⟩
    have hhit := mainWall_return_time_mem hh hτ hR hvalid (Nat.zero_lt_succ n)
    exact ⟨hhit, le_of_lt hhit.1, hT (mem_range_self (n + 1))⟩
  have hinfinite := infinite_range_of_injective (f := fun n => cumulativeReturnTime R τ t₀ (n + 1) y)
    (fun _ _ heq => Nat.add_right_cancel (hm.injective heq))
  exact hinfinite (hfinite.subset hsub)

theorem mainWallArrivalRelation_target_chart {k t : ℝ} {y : SectionCoordinates}
    (hh : 0 < h) (hy : (y, t) ∈ mainWallArrivalRelation h k t₀) :
    mainWallCoordinates (normalizedMaxCurve (mainWallChart h y) t₀ t) ∈ mainWallChartDomain k := by
  have hp := (maximalNormalizedSolution (mainWallChart h y) t₀).physical
    (mainWallChart_positive hh y) (mainWallChart_constraint hy.1) hy.2.1
  exact (mainWallChart_coordinates hp.1 hp.2 hy.2.2.2 hy.2.2.1).1

theorem mainWall_hittingTimes_after_time (hh : 0 < h) {y z : SectionCoordinates} {s t : ℝ}
    (hy : y ∈ mainWallChartDomain h) (hz : z ∈ mainWallChartDomain h) (hs : t₀ ≤ s)
    (hstate : mainWallChart h z = normalizedMaxCurve (mainWallChart h y) t₀ s) (ht : s < t) :
    t ∈ mainWallHittingTimes h h t₀ B (Ioi t₀) y ↔
      t₀ + (t - s) ∈ mainWallHittingTimes h h t₀ B (Ioi t₀) z := by
  have hu := normalizedMaxDomain_contains_Ici (mainWallChart_positive hh y)
    (mainWallChart_constraint hy) t₀ (show t₀ ≤ t₀ + (s - t₀) by linarith)
  have hv := normalizedMaxDomain_contains_Ici (mainWallChart_positive hh y)
    (mainWallChart_constraint hy) t₀ (show t₀ ≤ (t₀ + (t - s)) + (s - t₀) by linarith)
  have H := normalizedMaxCurve_shift hu hv
  rw [show t₀ + (s - t₀) = s by ring, ← hstate,
    show (t₀ + (t - s)) + (s - t₀) = t by ring] at H
  constructor
  · intro hhit
    refine ⟨show t₀ < t₀ + (t - s) by linarith, ⟨hz, ?_, ?_, ?_⟩, ?_⟩
    · exact normalizedMaxDomain_contains_Ici (mainWallChart_positive hh z)
        (mainWallChart_constraint hz) t₀ (show t₀ ≤ t₀ + (t - s) by linarith)
    · rw [H]
      exact hhit.2.1.2.2.1
    · rw [H]
      exact hhit.2.1.2.2.2
    · rw [H]
      exact hhit.2.2
  · intro hhit
    refine ⟨hs.trans_lt ht, ⟨hy, ?_, ?_, ?_⟩, ?_⟩
    · exact normalizedMaxDomain_contains_Ici (mainWallChart_positive hh y)
        (mainWallChart_constraint hy) t₀ (hs.trans ht.le)
    · rw [← H]
      exact hhit.2.1.2.2.1
    · rw [← H]
      exact hhit.2.1.2.2.2
    · rw [← H]
      exact hhit.2.2

/-- The cumulative times retain the first-return property on the original, un-restarted orbit. -/
theorem mainWall_return_next_time_isLeast (hh : 0 < h)
    (hτ : ∀ y ∈ mainWallReturnDomain h t₀ B,
      IsLeast (mainWallHittingTimes h h t₀ B (Ioi t₀) y) (τ y))
    (hR : ∀ y ∈ mainWallReturnDomain h t₀ B,
      R y = mainWallCoordinates (normalizedMaxCurve (mainWallChart h y) t₀ (τ y)))
    {y : SectionCoordinates} (hvalid : ∀ n, R^[n] y ∈ mainWallReturnDomain h t₀ B) (n : ℕ) :
    IsLeast (mainWallHittingTimes h h t₀ B (Ioi t₀) y ∩
      Ioi (cumulativeReturnTime R τ t₀ n y)) (cumulativeReturnTime R τ t₀ (n + 1) y) := by
  have hy : y ∈ mainWallChartDomain h := by simpa using (hτ _ (hvalid 0)).1.2.1.1
  have hz := (hτ _ (hvalid n)).1.2.1.1
  have hstate := mainWall_return_iterate_state hh hτ hR hy n (fun i _ => hvalid i)
  refine ⟨⟨mainWall_return_time_mem hh hτ hR hvalid (Nat.zero_lt_succ n),
    mainWall_return_times_strictMono hτ hvalid (Nat.lt_succ_self n)⟩, ?_⟩
  rintro t ⟨ht, hnt⟩
  have hlocal := (mainWall_hittingTimes_after_time hh hy hz hstate.1 hstate.2 hnt).mp ht
  have hmin := (hτ _ (hvalid n)).2 hlocal
  rw [cumulativeReturnTime_succ]
  linarith

end BianchiIX
