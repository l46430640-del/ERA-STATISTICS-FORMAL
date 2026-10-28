import BianchiIX.Measure.MainWallReturnOrbits

noncomputable section

namespace BianchiIX

open Set Filter

variable {h t₀ : ℝ} {B : Set SectionCoordinates}
  {R : SectionCoordinates → SectionCoordinates} {τ : SectionCoordinates → ℝ}

theorem mainWall_infinite_hittingTimes_iff_unbounded {ε : ℝ} {y : SectionCoordinates}
    (hh : 0 < h) (hε : 0 < ε) (hbound : ∀ z ∈ B, mainWallChart h z 0 ≤ -ε)
    (hy : y ∈ mainWallChartDomain h) :
    (mainWallHittingTimes h h t₀ B (Ioi t₀) y).Infinite ↔
      ¬ BddAbove (mainWallHittingTimes h h t₀ B (Ioi t₀) y) := by
  constructor
  · intro hinfinite hbounded
    obtain ⟨T, hT⟩ := hbounded
    have hfinite := finite_mainWallHittingTimes (t₀ := t₀) (T := T) (I := Ioi t₀) hh hh hε hy hbound
    exact hinfinite (hfinite.subset (fun t ht => ⟨ht, le_of_lt ht.1, hT ht⟩))
  · exact infinite_of_not_bddAbove

/-- Arbitrarily late physical returns make every iterate of the partial return map legal. -/
theorem mainWall_return_iterates_of_unbounded_hits (hh : 0 < h)
    (hτ : ∀ y ∈ mainWallReturnDomain h t₀ B,
      IsLeast (mainWallHittingTimes h h t₀ B (Ioi t₀) y) (τ y))
    (hR : ∀ y ∈ mainWallReturnDomain h t₀ B,
      R y = mainWallCoordinates (normalizedMaxCurve (mainWallChart h y) t₀ (τ y)))
    {y : SectionCoordinates} (hyB : y ∈ B) (hy : y ∈ mainWallChartDomain h)
    (hunbounded : ¬ BddAbove (mainWallHittingTimes h h t₀ B (Ioi t₀) y)) :
    ∀ n, R^[n] y ∈ mainWallReturnDomain h t₀ B := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hstate := mainWall_return_iterate_state hh hτ hR hy n ih
    have htarget : R^[n] y ∈ B ∧ R^[n] y ∈ mainWallChartDomain h := by
      cases n with
      | zero => simpa using And.intro hyB hy
      | succ m =>
        have hm := ih m (Nat.lt_succ_self m)
        rw [Function.iterate_succ_apply', hR _ hm]
        exact ⟨(hτ _ hm).1.2.2, mainWallArrivalRelation_target_chart hh (hτ _ hm).1.2.1⟩
    obtain ⟨t, ht, hnt⟩ := not_bddAbove_iff.mp hunbounded (cumulativeReturnTime R τ t₀ n y)
    have hhit := (mainWall_hittingTimes_after_time hh hy htarget.2 hstate.1 hstate.2 hnt).mp ht
    exact ⟨htarget.1, ⟨t₀ + (t - cumulativeReturnTime R τ t₀ n y), hhit⟩⟩

theorem mainWall_return_iterates_iff_infinite_hits (hh : 0 < h) {ε : ℝ} (hε : 0 < ε)
    (hbound : ∀ z ∈ B, mainWallChart h z 0 ≤ -ε)
    (hτ : ∀ y ∈ mainWallReturnDomain h t₀ B,
      IsLeast (mainWallHittingTimes h h t₀ B (Ioi t₀) y) (τ y))
    (hR : ∀ y ∈ mainWallReturnDomain h t₀ B,
      R y = mainWallCoordinates (normalizedMaxCurve (mainWallChart h y) t₀ (τ y)))
    {y : SectionCoordinates} (hyB : y ∈ B) (hy : y ∈ mainWallChartDomain h) :
    (∀ n, R^[n] y ∈ mainWallReturnDomain h t₀ B) ↔
      (mainWallHittingTimes h h t₀ B (Ioi t₀) y).Infinite := by
  constructor
  · intro hvalid
    have hm := mainWall_return_times_strictMono hτ hvalid
    apply (infinite_range_of_injective (f := fun n => cumulativeReturnTime R τ t₀ (n + 1) y)
      (fun _ _ heq => Nat.add_right_cancel (hm.injective heq))).mono
    rintro _ ⟨n, rfl⟩
    exact mainWall_return_time_mem hh hτ hR hvalid (Nat.zero_lt_succ n)
  · intro hinfinite
    exact mainWall_return_iterates_of_unbounded_hits hh hτ hR hyB hy
      ((mainWall_infinite_hittingTimes_iff_unbounded hh hε hbound hy).mp hinfinite)

/-- All physical positive hits are enumerated, with none skipped by the return iterates. -/
theorem mainWall_hittingTimes_eq_returnTime_range (hh : 0 < h) {ε : ℝ} (hε : 0 < ε)
    (hbound : ∀ z ∈ B, mainWallChart h z 0 ≤ -ε)
    (hτ : ∀ y ∈ mainWallReturnDomain h t₀ B,
      IsLeast (mainWallHittingTimes h h t₀ B (Ioi t₀) y) (τ y))
    (hR : ∀ y ∈ mainWallReturnDomain h t₀ B,
      R y = mainWallCoordinates (normalizedMaxCurve (mainWallChart h y) t₀ (τ y)))
    {y : SectionCoordinates} (hvalid : ∀ n, R^[n] y ∈ mainWallReturnDomain h t₀ B) :
    mainWallHittingTimes h h t₀ B (Ioi t₀) y =
      range (fun n => cumulativeReturnTime R τ t₀ (n + 1) y) := by
  ext t
  constructor
  · intro ht
    have hlim := mainWall_return_times_tendsto hh hε hbound hτ hR hvalid
    have hex : ∃ n, t ≤ cumulativeReturnTime R τ t₀ n y :=
      (hlim.eventually (eventually_ge_atTop t)).exists
    have hm := Nat.find_spec hex
    have hmpos : Nat.find hex ≠ 0 := by
      intro hz
      rw [hz, cumulativeReturnTime_zero] at hm
      exact (not_le_of_gt ht.1) hm
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hmpos
    have hprev : cumulativeReturnTime R τ t₀ n y < t :=
      lt_of_not_ge (Nat.find_min hex (by omega : n < Nat.find hex))
    have hnext := (mainWall_return_next_time_isLeast hh hτ hR hvalid n).2 ⟨ht, hprev⟩
    refine ⟨n, le_antisymm hnext ?_⟩
    simpa [hn] using hm
  · rintro ⟨n, rfl⟩
    exact mainWall_return_time_mem hh hτ hR hvalid (Nat.zero_lt_succ n)

end BianchiIX
