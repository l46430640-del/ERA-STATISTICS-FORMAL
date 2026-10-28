import BianchiIX.Dynamics.LateCompactCore

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

theorem eventually_normalizedWallProductsBound {x : NormalizedState}
    (H : ∀ i j : Fin 3, i ≠ j → Tendsto
      (fun t => wallValue i (normalizedMaxCurve x 0 t) * wallValue j (normalizedMaxCurve x 0 t)) atTop (𝓝 0))
    {Δ : ℝ} (hΔ : 0 < Δ) :
    ∀ᶠ t in atTop, normalizedWallProductsBound Δ (normalizedMaxCurve x 0 t) := by
  have hcut : 0 < Δ ^ 2 / 4 := by positivity
  filter_upwards [(H 0 1 (by decide)).eventually (gt_mem_nhds hcut),
    (H 1 2 (by decide)).eventually (gt_mem_nhds hcut),
    (H 2 0 (by decide)).eventually (gt_mem_nhds hcut)] with t h01 h12 h20
  change normalizedMaxCurve x 0 t 2 * normalizedMaxCurve x 0 t 3 < Δ ^ 2 / 4 at h01
  change normalizedMaxCurve x 0 t 3 * normalizedMaxCurve x 0 t 4 < Δ ^ 2 / 4 at h12
  change normalizedMaxCurve x 0 t 4 * normalizedMaxCurve x 0 t 2 < Δ ^ 2 / 4 at h20
  exact ⟨by nlinarith only [h01], by nlinarith only [h12], by nlinarith only [h20]⟩

/-- Eventual product smallness gives compact small cores after every prescribed original time. -/
theorem exists_arbitrarily_late_compact_core {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∃ γ > (0 : ℝ), γ < 1 / 4 ∧ ∀ B : ℝ, 0 < B →
      ∀ x : NormalizedState, stateConstraint x = 1 → positiveWalls x →
        (∀ᶠ t in atTop, ∀ i, ε ≤ normalizedEuclideanDistance (normalizedMaxCurve x 0 t) (taubPoint i)) →
        (∀ Δ : ℝ, 0 < Δ → ∀ᶠ t in atTop, normalizedWallProductsBound Δ (normalizedMaxCurve x 0 t)) →
        ∀ r : ℝ, ∃ T > max r 0, ∃ a : Fin 6, ∃ Y : CoreAngleState,
          T ∈ normalizedMaxDomain x 0 ∧
          fromProjectiveState (coreRadiusEntry Y) = (axisFrame a).map (normalizedMaxCurve x 0 T) ∧
          Y ∈ compactEraPhase N γ ∧ 0 < Y 1 ∧ 0 < Y 2 ∧ Y 1 + Y 2 ≤ B ∧
          normalizedTaubAvoidance ε (fromProjectiveState (coreRadiusEntry Y)) ∧
          0 < fderiv ℝ projectiveActiveWall (fromProjectiveState (coreRadiusEntry Y))
            (normalizedField (fromProjectiveState (coreRadiusEntry Y))) := by
  obtain ⟨N, γ, hγ, hγmax, H⟩ := exists_late_compact_core hε
  refine ⟨N, γ, hγ, hγmax, ?_⟩
  intro B hB x hc hp ha hprod r
  obtain ⟨Δ, hΔ, HΔ⟩ := H B hB
  obtain ⟨R, hR⟩ := eventually_atTop.mp ((hprod Δ hΔ).and ha)
  let s := max 0 (max r R)
  have hs : 0 ≤ s := le_max_left _ _
  have hsr : r ≤ s := (le_max_left _ _).trans (le_max_right _ _)
  have hsR : R ≤ s := (le_max_right _ _).trans (le_max_right _ _)
  have hdoms := normalizedMaxDomain_contains_Ici_of_constraint hc 0 hs
  let y := normalizedMaxCurve x 0 s
  have hcy : stateConstraint y = 1 := (normalizedMaxCurve_constraint hdoms).trans hc
  have hpy : positiveWalls y := normalized_positive_walls_invariant
    (convex_normalizedMaxDomain x 0) (isOpen_normalizedMaxDomain x 0)
    (fun _ ht => hasDerivAt_normalizedMaxCurve ht) (initial_mem_normalizedMaxDomain x 0)
    hdoms (by simpa only [normalizedMaxCurve_initial] using hp)
  have hshift (u : ℝ) (hu : 0 ≤ u) :
      normalizedMaxCurve x 0 (s + u) = normalizedMaxCurve y 0 u := by
    have Hs := (normalizedMaxCurve_restart (t := s + u) hdoms (by
      simpa only [add_sub_cancel_left] using normalizedMaxDomain_contains_Ici_of_constraint hcy 0 hu)).2
    simpa only [add_sub_cancel_left] using Hs
  have hprody (u : ℝ) (hu : 0 ≤ u) : normalizedWallProductsBound Δ (normalizedMaxCurve y 0 u) := by
    rw [← hshift u hu]
    exact (hR (s + u) (hsR.trans (le_add_of_nonneg_right hu))).1
  have hay : normalizedTaubAvoidance ε y := by
    intro u hu _ i
    rw [← hshift u hu]
    exact (hR (s + u) (hsR.trans (le_add_of_nonneg_right hu))).2 i
  obtain ⟨τ, hτ, a, Y, _, heq, hphase, hU, hW, hsum, havoid, htrans⟩ :=
    HΔ Δ ⟨hΔ.le, le_rfl⟩ y hcy hpy hay hprody
  have hT : max r 0 < s + τ := max_lt_iff.mpr
    ⟨by linarith only [hsr, hτ], by linarith only [hs, hτ]⟩
  refine ⟨s + τ, hT, a, Y,
    normalizedMaxDomain_contains_Ici_of_constraint hc 0 (add_nonneg hs hτ.le),
    ?_, hphase, hU, hW, hsum, havoid, htrans⟩
  rw [hshift τ hτ.le]
  exact heq

end BianchiIX
