import BianchiIX.Dynamics.ExitPhysicalRegion

noncomputable section

namespace BianchiIX

open Set

/-- A compact signed tail cannot wait longer than its logarithmic height budget in original normalized time. -/
theorem normalized_exit_residence {x : NormalizedState} {t₀ s t h : ℝ}
    (hc : stateConstraint x = 1) (hh : 0 < h) (hs : t₀ ≤ s) (hst : s ≤ t)
    (hA : ∀ u ∈ Icc s t, 0 < 1 + normalizedMaxCurve x t₀ u 0) :
    let β := fun u => toProjectiveState (normalizedMaxCurve x t₀ u)
    (∀ u ∈ Icc s t, exitPhysicalRegion h (β u)) → β s 2 = 1 →
    (t - s) / 16 ≤ -Real.log (β t 2) ∧ t - s ≤ 16 * Real.log (1 / h) := by
  intro β hregion hV
  let z := fun u => -Real.log (β u 2)
  let q := fun u => (1 + normalizedMaxCurve x t₀ u 0) * exitClockRate (β u)
  have hz (u : ℝ) (hu : u ∈ Icc s t) : HasDerivAt z (q u) u := by
    have H := normalizedMaxCurve_forward_of_constraint hc (hs.trans hu.1)
    exact hasDerivAt_exitLog_scaled
      (hasDerivAt_toProjectiveState_normalized H.1 (ne_of_gt (hA u hu)) H.2.1)
      (ne_of_gt (hh.trans_le (hregion u hu).2.2.2.1.1))
  have hq (u : ℝ) (hu : u ∈ Icc s t) : 1 / 16 ≤ q u := by
    have HA := normalized_exit_chart_lower hh (ne_of_gt (hA u hu))
      (normalizedMaxCurve_forward_of_constraint hc (hs.trans hu.1)).2.1 (hregion u hu)
    have HD := exitPhysicalRegion_clock hh (hregion u hu)
    have H := mul_le_mul HA HD (by norm_num : (0 : ℝ) ≤ 1 / 2) (hA u hu).le
    change 1 / 16 ≤ (1 + normalizedMaxCurve x t₀ u 0) * exitClockRate (β u)
    nlinarith only [H]
  have H := (convex_Icc s t).mul_sub_le_image_sub_of_le_deriv (HasDerivAt.continuousOn hz)
    (fun u hu => (hz u (interior_subset hu)).differentiableAt.differentiableWithinAt)
    (fun u hu => by rw [(hz u (interior_subset hu)).deriv]; exact hq u (interior_subset hu))
    s ⟨le_rfl, hst⟩ t ⟨hst, le_rfl⟩ hst
  have H' : (t - s) / 16 ≤ -Real.log (β t 2) := by
    change 1 / 16 * (t - s) ≤ -Real.log (β t 2) - -Real.log (β s 2) at H
    simpa only [hV, Real.log_one, neg_zero, sub_zero, one_div_mul_eq_div] using H
  refine ⟨H', ?_⟩
  have HL := Real.log_le_log hh (hregion t ⟨hst, le_rfl⟩).2.2.2.1.1
  rw [one_div, Real.log_inv]
  linarith only [H', HL]

end BianchiIX
