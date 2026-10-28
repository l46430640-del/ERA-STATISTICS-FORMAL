import BianchiIX.Dynamics.CorePrefix
import BianchiIX.Dynamics.CoreCrossings

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

def coreRegion (k : ℝ) (y : ProjectiveState) : Prop :=
  |coreEnergy (y 0) (y 2) - k ^ 2| ≤ 1 / 8 ∧ 1 ≤ y 2 ∧
    (0 ≤ y 1 ∧ y 1 ≤ (1 / 10000) / k) ∧
    (0 ≤ y 2 * y 3 ∧ y 2 * y 3 ≤ (1 / 10000) / k)

theorem coreRegion_radius_bounds {k : ℝ} {y : ProjectiveState} (hk : 6 ≤ k) (hy : coreRegion k y) :
    99 / 100 * k ≤ coreRadius (y 0) (y 2) ∧ coreRadius (y 0) (y 2) ≤ 101 / 100 * k :=
  coreBootstrap_radius_closed hk (Real.sqrt_nonneg _)
    (by rw [coreRadius_sq]; exact hy.1)

theorem coreRegion_wall_bounds {k : ℝ} {y : ProjectiveState} (hy : coreRegion k y) :
    (0 ≤ y 1 ∧ y 1 ≤ (1 / 10000) / k) ∧ (0 ≤ y 3 ∧ y 3 ≤ (1 / 10000) / k) := by
  have hv0 : 0 < y 2 := lt_of_lt_of_le zero_lt_one hy.2.1
  have hw0 : 0 ≤ y 3 := (mul_nonneg_iff_of_pos_left hv0).mp hy.2.2.2.1
  exact ⟨hy.2.2.1, hw0, (le_mul_of_one_le_left hw0 hy.2.1).trans hy.2.2.2.2⟩

theorem toProjectiveState_wall_sign {x : NormalizedState} (hA : 0 < 1 + x 0) (i : Fin 3) :
    (toProjectiveState x i.succ = 0 ↔ wallValue i x = 0) ∧
      (0 ≤ toProjectiveState x i.succ ↔ 0 ≤ wallValue i x) := by
  have heq : toProjectiveState x i.succ = Real.sqrt 3 * wallValue i x / (1 + x 0) := by
    fin_cases i <;> rfl
  have hsqrt : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  rw [heq]
  constructor
  · simp only [div_eq_zero_iff, mul_eq_zero, ne_of_gt hsqrt, ne_of_gt hA, false_or, or_false]
  · rw [div_eq_mul_inv, mul_nonneg_iff_of_pos_right (inv_pos.mpr hA), mul_nonneg_iff_of_pos_left hsqrt]

theorem normalized_projective_wall_sign {x : NormalizedState} {t₀ s t : ℝ}
    (hs : s ∈ normalizedMaxDomain x t₀) (ht : t ∈ normalizedMaxDomain x t₀)
    (hAs : 0 < 1 + normalizedMaxCurve x t₀ s 0) (hAt : 0 < 1 + normalizedMaxCurve x t₀ t 0)
    (i : Fin 3) :
    let β := fun u => toProjectiveState (normalizedMaxCurve x t₀ u)
    (β t i.succ = 0 ↔ β s i.succ = 0) ∧ (0 ≤ β t i.succ ↔ 0 ≤ β s i.succ) := by
  have H := normalized_wall_sign (convex_normalizedMaxDomain x t₀) (isOpen_normalizedMaxDomain x t₀)
    (fun _ hh => hasDerivAt_normalizedMaxCurve hh) hs ht i
  exact ⟨(toProjectiveState_wall_sign hAt i).1.trans (H.1.trans (toProjectiveState_wall_sign hAs i).1.symm),
    (toProjectiveState_wall_sign hAt i).2.trans (H.2.trans (toProjectiveState_wall_sign hAs i).2.symm)⟩

theorem eventually_lt_bound_of_deriv_inward {f : ℝ → ℝ} {s d B : ℝ}
    (hf : HasDerivAt f d s) (hle : f s ≤ B) (hinward : f s = B → d < 0) :
    ∀ᶠ t in 𝓝[>] s, f t < B := by
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact (hf.continuousAt.eventually (isOpen_Iio.mem_nhds hlt)).filter_mono nhdsWithin_le_nhds
  · simpa only [heq] using eventually_lt_right_of_deriv_neg hf (hinward heq)

/-- An inward or interior core state has a genuine right prefix, including saturated and zero walls. -/
theorem normalized_core_local_prefix {x : NormalizedState} {t₀ s k : ℝ}
    (hc : stateConstraint x = 1) (hk : 6 ≤ k) (hs : t₀ ≤ s)
    (hA : 0 < 1 + normalizedMaxCurve x t₀ s 0) :
    let β := fun u => toProjectiveState (normalizedMaxCurve x t₀ u)
    |coreEnergy (β s 0) (β s 2) - k ^ 2| < 1 / 8 →
    (1 < β s 2 ∨ (β s 2 = 1 ∧ 1 ≤ β s 0)) →
    (0 ≤ β s 1 ∧ β s 1 ≤ (1 / 10000) / k) →
    (0 ≤ β s 2 * β s 3 ∧ β s 2 * β s 3 ≤ (1 / 10000) / k) →
    ∃ r > s, ∀ u ∈ Icc s r,
      3 / (2 * k ^ 2) < 1 + normalizedMaxCurve x t₀ u 0 ∧ coreRegion k (β u) := by
  intro β he hvcase hu hp
  have hk0 : 0 < k := by linarith
  have hB : 0 < (1 / 10000 : ℝ) / k := div_pos (by norm_num) hk0
  have hv : 1 ≤ β s 2 := hvcase.elim (fun h => h.le) (fun h => le_of_eq h.1.symm)
  have hregion : coreRegion k (β s) := ⟨he.le, hv, hu, hp⟩
  have hr := coreRegion_radius_bounds hk hregion
  have hw := (coreRegion_wall_bounds hregion).2
  have hdom : ∀ u ≥ s, u ∈ normalizedMaxDomain x t₀ := fun u hh =>
    normalizedMaxDomain_contains_Ici_of_constraint hc t₀ (hs.trans hh)
  have hactual := normalizedMaxCurve_forward_of_constraint hc hs
  have hsol : HasDerivAt β ((1 + normalizedMaxCurve x t₀ s 0) • projectiveField (β s)) s :=
    hasDerivAt_toProjectiveState_normalized hactual.1 (ne_of_gt hA) hactual.2.1
  have hcoord (i : Fin 4) : ContinuousAt (fun u => β u i) s :=
    (hasDerivAt_pi.mp hsol i).continuousAt
  have hAc : ContinuousAt (fun u => 1 + normalizedMaxCurve x t₀ u 0) s :=
    continuousAt_const.add (hasDerivAt_pi.mp hactual.1 0).continuousAt
  have hEc : ContinuousAt (fun u => |coreEnergy (β u 0) (β u 2) - k ^ 2|) s := by
    unfold coreEnergy
    exact ((((hcoord 0).sub continuousAt_const).pow 2 |>.add ((hcoord 2).pow 2)).sub continuousAt_const).abs
  have hscale := (normalized_core_chart_bounds hk (ne_of_gt hA) hactual.2.1 hr.2
    (zero_le_one.trans hv) hu hw).1
  have hmargin : 3 / (2 * k ^ 2) < 1 + normalizedMaxCurve x t₀ s 0 := by
    have H : 3 / (2 * k ^ 2) < 3 / k ^ 2 := by
      apply (div_lt_div_iff₀ (by positivity) (by positivity)).mpr
      nlinarith [sq_pos_of_pos hk0]
    exact H.trans_le hscale
  have hU := hasDerivAt_pi.mp hsol 1
  have hUbound : ∀ᶠ u in 𝓝[>] s, β u 1 < (1 / 10000) / k := by
    apply eventually_lt_bound_of_deriv_inward hU hu.2
    intro hcap
    have H := mul_le_mul_of_nonneg_left (coreBootstrap_strong_velocity hk hr hu hw) hA.le
    change (1 + normalizedMaxCurve x t₀ s 0) * strongVelocity (β s 0) (β s 1) (β s 2) (β s 3) < 0
    apply H.trans_lt
    rw [hcap]
    exact mul_neg_of_pos_of_neg hA (mul_neg_of_neg_of_pos (by nlinarith [sq_pos_of_pos hk0]) hB)
  have hP : HasDerivAt (fun u => β u 2 * β u 3)
      ((1 + normalizedMaxCurve x t₀ s 0) * (-2 * (1 + coupling (β s 1) (β s 2) (β s 3)) * (β s 2 * β s 3))) s := by
    convert! (hasDerivAt_pi.mp hsol 2).mul (hasDerivAt_pi.mp hsol 3) using 1
    change _ = (1 + normalizedMaxCurve x t₀ s 0) * activeVelocity (β s 0) (β s 1) (β s 2) (β s 3) * β s 3 +
      β s 2 * ((1 + normalizedMaxCurve x t₀ s 0) * weakVelocity (β s 0) (β s 1) (β s 2) (β s 3))
    unfold activeVelocity weakVelocity
    ring
  have hPbound : ∀ᶠ u in 𝓝[>] s, β u 2 * β u 3 < (1 / 10000) / k := by
    apply eventually_lt_bound_of_deriv_inward hP hp.2
    intro hcap
    rw [hcap]
    have hC := coreBootstrap_coupling_nonneg hk hv hu hw.1
    exact mul_neg_of_pos_of_neg hA (mul_neg_of_neg_of_pos (by linarith) hB)
  have hVbound : ∀ᶠ u in 𝓝[>] s, 1 ≤ β u 2 := by
    rcases hvcase with hlt | ⟨hvone, hm⟩
    · exact ((hcoord 2).eventually (isOpen_Ioi.mem_nhds hlt)).filter_mono nhdsWithin_le_nhds |>.mono (fun _ h => h.le)
    · exact (scaled_core_entry_upward hk hA hsol hvone hm hr.1 hu hw).2.2.mono (fun _ h => h.le)
  have H : ∀ᶠ u in 𝓝[>] s,
      3 / (2 * k ^ 2) < 1 + normalizedMaxCurve x t₀ u 0 ∧
      |coreEnergy (β u 0) (β u 2) - k ^ 2| < 1 / 8 ∧ 1 ≤ β u 2 ∧
      β u 1 < (1 / 10000) / k ∧ β u 2 * β u 3 < (1 / 10000) / k := by
    filter_upwards [((hAc.eventually (isOpen_Ioi.mem_nhds hmargin)).filter_mono nhdsWithin_le_nhds),
      ((hEc.eventually (isOpen_Iio.mem_nhds he)).filter_mono nhdsWithin_le_nhds), hVbound, hUbound, hPbound]
      with u hAu hEu hVu hUu hPu
    exact ⟨hAu, hEu, hVu, hUu, hPu⟩
  obtain ⟨r, hsr, hsub⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp H
  refine ⟨r, hsr, ?_⟩
  intro u hsu
  rcases eq_or_lt_of_le hsu.1 with heq | hlt
  · subst u
    exact ⟨hmargin, hregion⟩
  have H := hsub ⟨hlt, hsu.2⟩
  have hAu : 0 < 1 + normalizedMaxCurve x t₀ u 0 :=
    lt_trans (by positivity : 0 < 3 / (2 * k ^ 2)) H.1
  have hU0 : 0 ≤ β u 1 :=
    (normalized_projective_wall_sign (hdom s le_rfl) (hdom u hlt.le) hA hAu 0).2.mpr hu.1
  have hW0 : 0 ≤ β u 3 :=
    (normalized_projective_wall_sign (hdom s le_rfl) (hdom u hlt.le) hA hAu 2).2.mpr hw.1
  exact ⟨H.1, H.2.1.le, H.2.2.1, ⟨hU0, H.2.2.2.1.le⟩,
    ⟨mul_nonneg (zero_le_one.trans H.2.2.1) hW0, H.2.2.2.2.le⟩⟩

end BianchiIX
