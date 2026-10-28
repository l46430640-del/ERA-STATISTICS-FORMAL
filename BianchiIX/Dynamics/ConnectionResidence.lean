import BianchiIX.Dynamics.ConnectionRegion

noncomputable section

namespace BianchiIX

open Set

/-- A connection prefix has bounded length in normalized time, even for arbitrarily small W. -/
theorem normalized_connection_residence {x : NormalizedState} {t₀ μ s t : ℝ}
    (hc : stateConstraint x = 1) (hμ : 4 ≤ μ) (hs : t₀ ≤ s) (hst : s ≤ t)
    (hA : ∀ u ∈ Icc s t, 0 < 1 + normalizedMaxCurve x t₀ u 0) :
    let β := fun u => toProjectiveState (normalizedMaxCurve x t₀ u);
    (∀ u ∈ Icc s t, connectionRegion μ (β u)) → (∀ u ∈ Icc s t, 0 < β u 3) →
    (t - s) / μ ≤ Real.log (β t 3) - Real.log (β s 3) ∧
      t - s ≤ μ * Real.log (1 / β s 3) := by
  intro β hregion hw
  have hμ0 : 0 < μ := by linarith only [hμ]
  let z := fun u => Real.log (β u 3)
  let q := fun u => (1 + normalizedMaxCurve x t₀ u 0) * connectionClockRate (β u)
  have hz (u : ℝ) (hh : u ∈ Icc s t) : HasDerivAt z (q u) u := by
    have H := normalizedMaxCurve_forward_of_constraint hc (hs.trans hh.1)
    exact hasDerivAt_connectionLog_scaled
      (hasDerivAt_toProjectiveState_normalized H.1 (ne_of_gt (hA u hh)) H.2.1) (ne_of_gt (hw u hh))
  have hq (u : ℝ) (hh : u ∈ Icc s t) : 1 / μ ≤ q u := by
    have H := connection_original_clock_lower hμ (hregion u hh).1 (hregion u hh).2.1
      (hregion u hh).2.2.1 (hregion u hh).2.2.2
    simp only [neg_neg] at H
    have hc' := (normalizedMaxCurve_forward_of_constraint hc (hs.trans hh.1)).2.1
    have heq := projective_inverse_scale (ne_of_gt (hA u hh)) hc'
    change 6 / projectiveStateDenom (β u) = 1 + normalizedMaxCurve x t₀ u 0 at heq
    change 1 / μ ≤ (6 / projectiveStateDenom (β u)) * connectionClockRate (β u) at H
    rwa [heq] at H
  have H := (convex_Icc s t).mul_sub_le_image_sub_of_le_deriv (HasDerivAt.continuousOn hz)
    (fun u hh => (hz u (interior_subset hh)).differentiableAt.differentiableWithinAt)
    (fun u hh => by rw [(hz u (interior_subset hh)).deriv]; exact hq u (interior_subset hh))
    s ⟨le_rfl, hst⟩ t ⟨hst, le_rfl⟩ hst
  have H' : (t - s) / μ ≤ z t - z s := by simpa only [one_div_mul_eq_div] using H
  refine ⟨H', ?_⟩
  have hzt : z t ≤ 0 := Real.log_nonpos (hw t ⟨hst, le_rfl⟩).le (hregion t ⟨hst, le_rfl⟩).2.2.2.2
  have hL : (t - s) / μ ≤ Real.log (1 / β s 3) := by
    rw [one_div, Real.log_inv]
    linarith only [H', hzt]
  have H'' := (div_le_iff₀ hμ0).mp hL
  nlinarith only [H'']

end BianchiIX
