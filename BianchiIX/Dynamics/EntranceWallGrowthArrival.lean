import BianchiIX.Dynamics.EntranceWallSolutionGrowth

noncomputable section

namespace BianchiIX

open Set MeasureTheory

theorem exists_normalized_entrance_wall_solution_growth :
    ∃ C > (0 : ℝ), ∀ (x : NormalizedState) (t₀ s t k : ℝ),
      stateConstraint x = 1 → 7 / 4 ≤ k → t₀ ≤ s → s ≤ t →
      (∀ r ∈ Icc s t, 0 < normalizedProjectiveRate x t₀ r) →
      let Y := fun r => toProjectiveState (normalizedMaxCurve x t₀ r)
      (∀ r ∈ Icc s t, entranceRegion k (Y r)) → 0 < Y s 2 →
      ∀ b c : ℝ, s ≤ b → b ≤ c → c ≤ t →
      ∀ f p : ℝ → (Fin 2 → ℝ), ContinuousOn p (Icc b c) →
      (∀ r ∈ Icc b c, HasDerivAt f
        (((normalizedProjectiveRate x t₀ r * entranceClockRate (Y r)) •
          entranceWallWeightedMatrix k (Y r)).mulVec (f r) + p r) r) →
      ‖f c - f b‖ ≤ C * (Y s 1 * |f b 0| + Y s 3 / k ^ 2 * |f b 1| + ∫ r in b..c, ‖p r‖) := by
  obtain ⟨C, hC, HC⟩ := exists_scaled_entrance_wall_solution_growth
  refine ⟨C, hC, ?_⟩
  intro x t₀ s t k hc hk hs hst hA Y hy hvs
  have hdom (r : ℝ) (hr : s ≤ r) := normalizedMaxDomain_contains_Ici_of_constraint hc t₀ (hs.trans hr)
  have hY (r : ℝ) (hr : r ∈ Icc s t) : HasDerivAt Y
      (normalizedProjectiveRate x t₀ r • projectiveField (Y r)) r := by
    have H := normalizedMaxCurve_forward_of_constraint hc (hs.trans hr.1)
    exact hasDerivAt_toProjectiveState_normalized H.1 (hA r hr).ne' H.2.1
  have hv (r : ℝ) (hr : r ∈ Icc s t) : 0 < Y r 2 :=
    normalized_projective_wall_pos (hdom s le_rfl) (hdom r hr.1)
      (hA s ⟨le_rfl, hst⟩) (hA r hr) 1 hvs
  have hac : ContinuousOn (normalizedProjectiveRate x t₀) (Icc s t) :=
    (continuousOn_normalizedProjectiveRate x t₀).mono (fun r hr => hdom r hr.1)
  exact HC Y (normalizedProjectiveRate x t₀) s t k hk hst hY hac (fun r hr => (hA r hr).le) hy hv

/-- The growth estimate holds on every subinterval of the actual first entrance passage. -/
theorem exists_entrance_first_arrival_wall_solution_growth :
    ∃ C > (0 : ℝ), ∀ (x : NormalizedState) (t₀ s k : ℝ),
      stateConstraint x = 1 → 7 / 4 ≤ k → t₀ ≤ s → 0 < normalizedProjectiveRate x t₀ s →
      let Y := fun r => toProjectiveState (normalizedMaxCurve x t₀ r)
      1 ≤ Y s 0 → coreRadius (Y s 0) (Y s 2) = k →
      (0 ≤ Y s 1 ∧ Y s 1 ≤ 1 / 10000) → (0 < Y s 2 ∧ Y s 2 < 1) →
      (0 ≤ Y s 3 ∧ Y s 3 ≤ 1 / 10000) →
      ∃ t > s, Y t 2 = 1 ∧ (∀ r ∈ Ico s t, Y r 2 < 1) ∧
        (∀ r ∈ Icc s t, 1 / (2 * (k + 1) ^ 2) ≤ normalizedProjectiveRate x t₀ r ∧ entranceRegion k (Y r)) ∧
        ∀ b c : ℝ, s ≤ b → b ≤ c → c ≤ t →
        ∀ f p : ℝ → (Fin 2 → ℝ), ContinuousOn p (Icc b c) →
        (∀ r ∈ Icc b c, HasDerivAt f
          (((normalizedProjectiveRate x t₀ r * entranceClockRate (Y r)) •
            entranceWallWeightedMatrix k (Y r)).mulVec (f r) + p r) r) →
        ‖f c - f b‖ ≤ C * (Y s 1 * |f b 0| + Y s 3 / k ^ 2 * |f b 1| + ∫ r in b..c, ‖p r‖) := by
  obtain ⟨C, hC, HC⟩ := exists_normalized_entrance_wall_solution_growth
  refine ⟨C, hC, ?_⟩
  intro x t₀ s k hc hk hs hA Y hm hR hu hv hw
  obtain ⟨t, hst, hhit, hbefore, hregion, _⟩ :=
    exists_normalized_entrance_first_arrival hc hk hs hA hm hR hu hv hw
  have hK : 0 < k + 1 := by linarith
  have hpos : 0 < 1 / (2 * (k + 1) ^ 2) := by positivity
  refine ⟨t, hst, hhit, hbefore, hregion, ?_⟩
  exact HC x t₀ s t k hc hk hs hst.le (fun r hr => hpos.trans_le (hregion r hr).1)
    (fun r hr => (hregion r hr).2) hv.1

end BianchiIX
