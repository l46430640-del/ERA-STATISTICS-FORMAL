import BianchiIX.Dynamics.ConnectionRegion

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

/-- Interior phase and an uncompleted connection have a genuine right prefix, including U = 0. -/
theorem normalized_connection_local_prefix {x : NormalizedState} {t₀ s μ : ℝ}
    (hc : stateConstraint x = 1) (hμ : 4 ≤ μ) (hs : t₀ ≤ s)
    (hA : 0 < 1 + normalizedMaxCurve x t₀ s 0) :
    let β := fun u => toProjectiveState (normalizedMaxCurve x t₀ u);
    |-β s 0 - μ| < 1 / 2 →
    (0 ≤ β s 1 ∧ β s 1 ≤ 1 / 10000) →
    (0 < β s 2 ∧ β s 2 ≤ 1) → (0 < β s 3 ∧ β s 3 < 1) →
    ∃ r > s, ∀ u ∈ Icc s r,
      3 / (2 * μ ^ 2) < 1 + normalizedMaxCurve x t₀ u 0 ∧ connectionRegion μ (β u) := by
  intro β hm hu hv hw
  have hμ0 : 0 < μ := by linarith only [hμ]
  have hregion : connectionRegion μ (β s) := ⟨hm.le, hu, ⟨hv.1.le, hv.2⟩, hw.1.le, hw.2.le⟩
  have hdom : ∀ u ≥ s, u ∈ normalizedMaxDomain x t₀ := fun u hh =>
    normalizedMaxDomain_contains_Ici_of_constraint hc t₀ (hs.trans hh)
  have hactual := normalizedMaxCurve_forward_of_constraint hc hs
  have hsol : HasDerivAt β ((1 + normalizedMaxCurve x t₀ s 0) • projectiveField (β s)) s :=
    hasDerivAt_toProjectiveState_normalized hactual.1 (ne_of_gt hA) hactual.2.1
  have hcoord (i : Fin 4) : ContinuousAt (fun u => β u i) s :=
    (hasDerivAt_pi.mp hsol i).continuousAt
  have hAc : ContinuousAt (fun u => 1 + normalizedMaxCurve x t₀ u 0) s :=
    continuousAt_const.add (hasDerivAt_pi.mp hactual.1 0).continuousAt
  have hmc : ContinuousAt (fun u => |-β u 0 - μ|) s := ((hcoord 0).neg.sub continuousAt_const).abs
  have hscale := normalized_connection_chart_lower hμ (ne_of_gt hA) hactual.2.1 hregion
  have hmargin : 3 / (2 * μ ^ 2) < 1 + normalizedMaxCurve x t₀ s 0 := by
    apply lt_of_lt_of_le _ hscale
    apply (div_lt_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith only [sq_pos_of_pos hμ0]
  have hUbound : ∀ᶠ u in 𝓝[>] s, β u 1 < 1 / 10000 := by
    apply eventually_lt_bound_of_deriv_inward (hasDerivAt_pi.mp hsol 1) hu.2
    intro hcap
    have hr := connection_strong_rate_le (v := β s 2) (w := β s 3) hμ hm.le hu
    have hrneg : connectionStrongRate (-β s 0) (β s 1) (β s 2) (β s 3) < 0 :=
      hr.trans_lt (by nlinarith only [sq_pos_of_pos hμ0])
    have hu0 : 0 < β s 1 := by rw [hcap]; norm_num
    have hstrong : strongVelocity (β s 0) (β s 1) (β s 2) (β s 3) < 0 := by
      convert! mul_neg_of_neg_of_pos hrneg hu0 using 1
      dsimp [strongVelocity, connectionStrongRate]
      ring
    exact mul_neg_of_pos_of_neg hA hstrong
  have hVbound : ∀ᶠ u in 𝓝[>] s, β u 2 < 1 := by
    apply eventually_lt_bound_of_deriv_inward (hasDerivAt_pi.mp hsol 2) hv.2
    intro _
    have hr := connection_active_rate_neg hμ hm.le hu ⟨hv.1.le, hv.2⟩ ⟨hw.1.le, hw.2.le⟩
    simp only [neg_neg] at hr
    exact mul_neg_of_pos_of_neg hA (mul_neg_of_neg_of_pos hr hv.1)
  have H : ∀ᶠ u in 𝓝[>] s,
      3 / (2 * μ ^ 2) < 1 + normalizedMaxCurve x t₀ u 0 ∧
      |-β u 0 - μ| < 1 / 2 ∧ β u 1 < 1 / 10000 ∧ β u 2 < 1 ∧ β u 3 < 1 := by
    filter_upwards [(hAc.eventually (isOpen_Ioi.mem_nhds hmargin)).filter_mono nhdsWithin_le_nhds,
      (hmc.eventually (isOpen_Iio.mem_nhds hm)).filter_mono nhdsWithin_le_nhds, hUbound, hVbound,
      ((hcoord 3).eventually (isOpen_Iio.mem_nhds hw.2)).filter_mono nhdsWithin_le_nhds]
      with u hAu hmu hUu hVu hWu
    exact ⟨hAu, hmu, hUu, hVu, hWu⟩
  obtain ⟨r, hsr, hsub⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp H
  refine ⟨r, hsr, ?_⟩
  intro u hsu
  rcases eq_or_lt_of_le hsu.1 with heq | hlt
  · subst u
    exact ⟨hmargin, hregion⟩
  have H := hsub ⟨hlt, hsu.2⟩
  have hAu : 0 < 1 + normalizedMaxCurve x t₀ u 0 :=
    lt_trans (by positivity : 0 < 3 / (2 * μ ^ 2)) H.1
  have hU0 := (normalized_projective_wall_sign (hdom s le_rfl) (hdom u hlt.le) hA hAu 0).2.mpr hu.1
  have hV0 := (normalized_projective_wall_sign (hdom s le_rfl) (hdom u hlt.le) hA hAu 1).2.mpr hv.1.le
  have hW0 := (normalized_projective_wall_sign (hdom s le_rfl) (hdom u hlt.le) hA hAu 2).2.mpr hw.1.le
  exact ⟨H.1, H.2.1.le, ⟨hU0, H.2.2.1.le⟩, ⟨hV0, H.2.2.2.1.le⟩, hW0, H.2.2.2.2.le⟩

end BianchiIX
