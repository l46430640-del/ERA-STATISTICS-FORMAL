import BianchiIX.Dynamics.ConnectionFirstReturn
import BianchiIX.Dynamics.ConnectionLogSegment
import BianchiIX.Dynamics.ConnectionPhaseEndpoint

noncomputable section

namespace BianchiIX

open Set

theorem normalized_connection_endpoint_phase_bound {x : NormalizedState} {t₀ μ s t : ℝ}
    (hc : stateConstraint x = 1) (hμ : 4 ≤ μ) (hs : t₀ ≤ s) (hst : s ≤ t)
    (hA : ∀ u ∈ Icc s t, 0 < 1 + normalizedMaxCurve x t₀ u 0) :
    let β := fun u => toProjectiveState (normalizedMaxCurve x t₀ u);
    (∀ u ∈ Icc s t, connectionRegion μ (β u)) → -β s 0 = μ → β s 2 = 1 →
    0 < β s 3 → β t 3 = 1 →
    |phaseNorm (-β t 0 - 1) 1 - phaseNorm (μ + 1) 1 + 2| ≤ 24 * (β s 1 + (β s 3) ^ 2) / μ := by
  intro β hregion hinit hV hw hhit
  obtain ⟨hL, q, hq0, hqt, hqmap, _, hqode⟩ :=
    exists_normalized_connection_log_segment hc hμ hs hst hA hregion hw
  have hsm : s ∈ Icc s t := ⟨le_rfl, hst⟩
  have hdom (u : ℝ) (hu : u ∈ Icc s t) : u ∈ normalizedMaxDomain x t₀ :=
    normalizedMaxDomain_contains_Ici_of_constraint hc t₀ (hs.trans hu.1)
  have hvpos (u : ℝ) (hu : u ∈ Icc s t) : 0 < β u 2 := by
    apply normalized_projective_wall_pos (hdom s hsm) (hdom u hu) (hA s hsm) (hA u hu) 1
    change 0 < β s 2
    rw [hV]
    norm_num
  have H := connectionLog_endpoint_phase_bound hL hμ hqode
    (fun z hz => (hregion _ (hqmap hz)).1)
    (fun z hz => (hregion _ (hqmap hz)).2.1)
    (fun z hz => ⟨hvpos _ (hqmap hz), (hregion _ (hqmap hz)).2.2.1.2⟩)
    (fun z hz => (hregion _ (hqmap hz)).2.2.2)
    (by change -β (q 0) 0 = μ; rwa [hq0])
    (by change β (q 0) 2 = 1; rwa [hq0])
    (by change β (q _) 3 = 1; rwa [hqt])
  simpa only [hq0, hqt] using H

/-- The actual first connection satisfies (B.5) with the explicit universal constant 24. -/
theorem exists_connection_phase_bound {μ u w : ℝ} (hμ : 4 ≤ μ)
    (hu : 0 ≤ u ∧ u ≤ (1 / 10000) / μ) (hw : 0 < w ∧ w ≤ 1 / 10000) :
    let x := fromProjectiveState (connectionEntry μ u w)
    let β := fun t => toProjectiveState (normalizedMaxCurve x 0 t)
    ∃ T > (0 : ℝ),
      IsLeast {t | 0 < t ∧ t ∈ normalizedMaxDomain x 0 ∧ β t 3 = 1} T ∧
      (∀ t ∈ Icc 0 T, 3 / (2 * μ ^ 2) ≤ 1 + normalizedMaxCurve x 0 t 0 ∧ connectionRegion μ (β t)) ∧
      |phaseNorm (-β T 0 - 1) 1 - phaseNorm (μ + 1) 1 + 2| ≤ 24 * (u + w ^ 2) / μ := by
  intro x β
  obtain ⟨T, hT, hfirst, hprefix, _⟩ := exists_connection_first_return hμ hu hw
  have hμ1 : 1 ≤ μ := by linarith only [hμ]
  have hu' : 0 ≤ u ∧ u ≤ 1 / 10000 := ⟨hu.1, hu.2.trans (div_le_self (by norm_num) hμ1)⟩
  have hw' : 0 ≤ w ∧ w ≤ 1 := ⟨hw.1.le, hw.2.trans (by norm_num)⟩
  have hD : 0 < projectiveStateDenom (connectionEntry μ u w) :=
    (connection_denom_bound (m := μ) (v := 1) hu' (by norm_num) hw').2
  have hc : stateConstraint x = 1 := fromProjectiveState_constraint (ne_of_gt hD)
  have hβ0 : β 0 = connectionEntry μ u w := by
    dsimp [β]
    rw [normalizedMaxCurve_initial]
    exact toProjectiveState_fromProjectiveState (ne_of_gt hD)
  have hA (t : ℝ) (ht : t ∈ Icc 0 T) : 0 < 1 + normalizedMaxCurve x 0 t 0 :=
    lt_of_lt_of_le (by positivity) (hprefix t ht).1
  have H := normalized_connection_endpoint_phase_bound hc hμ (le_refl 0) hT.le hA
    (fun t ht => (hprefix t ht).2)
    (show -β 0 0 = μ by rw [hβ0]; simp [connectionEntry])
    (show β 0 2 = 1 by rw [hβ0]; rfl)
    (show 0 < β 0 3 by simpa [hβ0, connectionEntry] using hw.1) hfirst.1.2.2
  refine ⟨T, hT, hfirst, hprefix, ?_⟩
  change |phaseNorm (-β T 0 - 1) 1 - phaseNorm (μ + 1) 1 + 2| ≤
    24 * (β 0 1 + (β 0 3) ^ 2) / μ at H
  simpa [hβ0, connectionEntry] using H

end BianchiIX
