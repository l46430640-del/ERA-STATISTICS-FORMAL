import BianchiIX.Dynamics.ConnectionRegion

noncomputable section

namespace BianchiIX

open Set

theorem connection_scaled_wall_rates {y : ProjectiveState} {μ a : ℝ}
    (hμ : 4 ≤ μ) (ha : 0 < a) (hy : connectionRegion μ y) (hv : 0 < y 2) (hw : 0 < y 3) :
    a * projectiveField y 2 < 0 ∧ 0 < a * projectiveField y 3 := by
  have hr := connection_active_rate_neg hμ hy.1 hy.2.1 hy.2.2.1 hy.2.2.2
  simp only [neg_neg] at hr
  have hD : 0 < connectionClockRate y := by
    have H := (connection_speed_bounds hμ hy.1 hy.2.1 hy.2.2.1 hy.2.2.2).1
    change μ / 2 ≤ connectionClockRate y at H
    linarith only [H, hμ]
  exact ⟨mul_neg_of_pos_of_neg ha (mul_neg_of_neg_of_pos hr hv),
    mul_pos ha (mul_pos hD hw)⟩

theorem scaled_connection_monotonicity {β : ℝ → ProjectiveState} {a : ℝ → ℝ}
    {I : Set ℝ} {μ : ℝ} (hI : Convex ℝ I) (hμ : 4 ≤ μ)
    (ha : ∀ u ∈ I, 0 < a u)
    (hβ : ∀ u ∈ I, HasDerivAt β (a u • projectiveField (β u)) u)
    (hy : ∀ u ∈ I, connectionRegion μ (β u))
    (hv : ∀ u ∈ I, 0 < β u 2) (hw : ∀ u ∈ I, 0 < β u 3) :
    StrictAntiOn (fun u => β u 2) I ∧ StrictMonoOn (fun u => β u 3) I := by
  have hd (i : Fin 4) (u : ℝ) (hu : u ∈ I) := hasDerivAt_pi.mp (hβ u hu) i
  constructor
  · apply strictAntiOn_of_deriv_neg hI (fun u hu => (hd 2 u hu).continuousAt.continuousWithinAt)
    intro u hu
    rw [(hd 2 u (interior_subset hu)).deriv]
    exact (connection_scaled_wall_rates hμ (ha u (interior_subset hu)) (hy u (interior_subset hu))
      (hv u (interior_subset hu)) (hw u (interior_subset hu))).1
  · apply strictMonoOn_of_deriv_pos hI (fun u hu => (hd 3 u hu).continuousAt.continuousWithinAt)
    intro u hu
    rw [(hd 3 u (interior_subset hu)).deriv]
    exact (connection_scaled_wall_rates hμ (ha u (interior_subset hu)) (hy u (interior_subset hu))
      (hv u (interior_subset hu)) (hw u (interior_subset hu))).2

theorem normalized_connection_monotonicity {x : NormalizedState} {t₀ μ s t : ℝ}
    (hc : stateConstraint x = 1) (hμ : 4 ≤ μ) (hs : t₀ ≤ s) (hst : s ≤ t)
    (hA : ∀ u ∈ Icc s t, 0 < 1 + normalizedMaxCurve x t₀ u 0) :
    let β := fun u => toProjectiveState (normalizedMaxCurve x t₀ u);
    (∀ u ∈ Icc s t, connectionRegion μ (β u)) → 0 < β s 2 → 0 < β s 3 →
    StrictAntiOn (fun u => β u 2) (Icc s t) ∧ StrictMonoOn (fun u => β u 3) (Icc s t) := by
  intro β hy hv hw
  have hdom (u : ℝ) (hu : s ≤ u) : u ∈ normalizedMaxDomain x t₀ :=
    normalizedMaxDomain_contains_Ici_of_constraint hc t₀ (hs.trans hu)
  have hAs := hA s ⟨le_rfl, hst⟩
  apply scaled_connection_monotonicity (a := fun u => 1 + normalizedMaxCurve x t₀ u 0)
    (convex_Icc s t) hμ hA ?_ hy ?_ ?_
  · intro u hu
    have H := normalizedMaxCurve_forward_of_constraint hc (hs.trans hu.1)
    exact hasDerivAt_toProjectiveState_normalized H.1 (ne_of_gt (hA u hu)) H.2.1
  · intro u hu
    exact normalized_projective_wall_pos (hdom s le_rfl) (hdom u hu.1) hAs (hA u hu) 1 hv
  · intro u hu
    exact normalized_projective_wall_pos (hdom s le_rfl) (hdom u hu.1) hAs (hA u hu) 2 hw

end BianchiIX
