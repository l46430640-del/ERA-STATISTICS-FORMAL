import BianchiIX.Dynamics.EntranceDrift
import BianchiIX.Dynamics.ConnectionEntry

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

theorem normalized_entrance_local_prefix {x : NormalizedState} {t₀ s k : ℝ}
    (hc : stateConstraint x = 1) (hk : 7 / 4 ≤ k) (hs : t₀ ≤ s)
    (hA : 0 < normalizedProjectiveRate x t₀ s) :
    let Y := fun r => toProjectiveState (normalizedMaxCurve x t₀ r)
    1 ≤ Y s 0 → |coreRadius (Y s 0) (Y s 2) - k| < k / 100 →
    (0 ≤ Y s 1 ∧ Y s 1 ≤ 1 / 10000) → (0 < Y s 2 ∧ Y s 2 < 1) →
    (0 ≤ Y s 3 ∧ Y s 3 ≤ 1 / 10000) →
    ∃ r > s, ∀ b ∈ Icc s r,
      1 / (2 * (k + 1) ^ 2) < normalizedProjectiveRate x t₀ b ∧ entranceRegion k (Y b) := by
  intro Y hm hR hu hv hw
  have hk0 : 0 < k := by linarith
  have hK : 0 < k + 1 := by linarith
  have hregion : entranceRegion k (Y s) := ⟨hm, hR.le, hu, ⟨hv.1.le, hv.2.le⟩, hw⟩
  have hactual := normalizedMaxCurve_forward_of_constraint hc hs
  have hsol : HasDerivAt Y (normalizedProjectiveRate x t₀ s • projectiveField (Y s)) s :=
    hasDerivAt_toProjectiveState_normalized hactual.1 hA.ne' hactual.2.1
  have hcoord (i : Fin 4) : ContinuousAt (fun b => Y b i) s := (hasDerivAt_pi.mp hsol i).continuousAt
  have hAc : ContinuousAt (normalizedProjectiveRate x t₀) s :=
    continuousAt_const.add (hasDerivAt_pi.mp hactual.1 0).continuousAt
  have hRc : ContinuousAt (fun b => |coreRadius (Y b 0) (Y b 2) - k|) s := by
    unfold coreRadius coreEnergy
    fun_prop
  have hms : 1 < Y s 0 := by linarith [(entranceRegion_phase hk hregion).1]
  have hscale := normalized_entrance_chart_lower hk hA.ne' hactual.2.1 hregion
  have hmargin : 1 / (2 * (k + 1) ^ 2) < normalizedProjectiveRate x t₀ s := by
    apply lt_of_lt_of_le _ hscale
    apply (div_lt_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith only [sq_pos_of_pos hK]
  have hD := entranceRegion_clock_pos hk hregion
  have hrates := entranceRegion_wall_rates hk hregion
  have hUbound : ∀ᶠ b in 𝓝[>] s, Y b 1 < 1 / 10000 := by
    apply eventually_lt_bound_of_deriv_inward (hasDerivAt_pi.mp hsol 1) hu.2
    intro hcap
    have hrate : connectionStrongRate (Y s 0) (Y s 1) (Y s 2) (Y s 3) < 0 :=
      ((div_le_iff₀ hD).mp hrates.1).trans_lt (mul_neg_of_neg_of_pos (by linarith) hD)
    have hwall : 0 < Y s 1 := by rw [hcap]; norm_num
    have hvel : strongVelocity (Y s 0) (Y s 1) (Y s 2) (Y s 3) < 0 := by
      convert! mul_neg_of_neg_of_pos hrate hwall using 1
      unfold strongVelocity connectionStrongRate
      ring
    exact mul_neg_of_pos_of_neg hA hvel
  have hWbound : ∀ᶠ b in 𝓝[>] s, Y b 3 < 1 / 10000 := by
    apply eventually_lt_bound_of_deriv_inward (hasDerivAt_pi.mp hsol 3) hw.2
    intro hcap
    have hrate : -Y s 0 - 1 - coupling (Y s 1) (Y s 2) (Y s 3) < 0 :=
      ((div_le_iff₀ hD).mp hrates.2).trans_lt (mul_neg_of_neg_of_pos (by have := one_div_pos.mpr hk0; linarith) hD)
    have hwall : 0 < Y s 3 := by rw [hcap]; norm_num
    exact mul_neg_of_pos_of_neg hA (mul_neg_of_neg_of_pos hrate hwall)
  have H : ∀ᶠ b in 𝓝[>] s,
      1 / (2 * (k + 1) ^ 2) < normalizedProjectiveRate x t₀ b ∧ 1 < Y b 0 ∧
      |coreRadius (Y b 0) (Y b 2) - k| < k / 100 ∧ Y b 1 < 1 / 10000 ∧ Y b 2 < 1 ∧ Y b 3 < 1 / 10000 := by
    filter_upwards [(hAc.eventually (isOpen_Ioi.mem_nhds hmargin)).filter_mono nhdsWithin_le_nhds,
      ((hcoord 0).eventually (isOpen_Ioi.mem_nhds hms)).filter_mono nhdsWithin_le_nhds,
      (hRc.eventually (isOpen_Iio.mem_nhds hR)).filter_mono nhdsWithin_le_nhds, hUbound,
      ((hcoord 2).eventually (isOpen_Iio.mem_nhds hv.2)).filter_mono nhdsWithin_le_nhds, hWbound]
      with b hAb hmb hRb hub hvb hwb
    exact ⟨hAb, hmb, hRb, hub, hvb, hwb⟩
  obtain ⟨r, hsr, hsub⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp H
  refine ⟨r, hsr, ?_⟩
  intro b hb
  rcases eq_or_lt_of_le hb.1 with heq | hlt
  · subst b
    exact ⟨hmargin, hregion⟩
  have Hb := hsub ⟨hlt, hb.2⟩
  have hAb : 0 < normalizedProjectiveRate x t₀ b :=
    lt_trans (by positivity : 0 < 1 / (2 * (k + 1) ^ 2)) Hb.1
  have hdom (c : ℝ) (hh : s ≤ c) := normalizedMaxDomain_contains_Ici_of_constraint hc t₀ (hs.trans hh)
  have hwall (i : Fin 3) := (normalized_projective_wall_sign (hdom s le_rfl) (hdom b hlt.le) hA hAb i).2
  exact ⟨Hb.1, Hb.2.1.le, Hb.2.2.1.le, ⟨(hwall 0).mpr hu.1, Hb.2.2.2.1.le⟩,
    ⟨(hwall 1).mpr hv.1.le, Hb.2.2.2.2.1.le⟩, (hwall 2).mpr hw.1, Hb.2.2.2.2.2.le⟩

theorem normalized_entrance_residence {x : NormalizedState} {t₀ s t k : ℝ}
    (hc : stateConstraint x = 1) (hk : 7 / 4 ≤ k) (hs : t₀ ≤ s) (hst : s ≤ t)
    (hA : ∀ r ∈ Icc s t, 0 < normalizedProjectiveRate x t₀ r) :
    let Y := fun r => toProjectiveState (normalizedMaxCurve x t₀ r)
    (∀ r ∈ Icc s t, entranceRegion k (Y r)) → 0 < Y s 2 →
    k / (2 * (k + 1) ^ 2) * (t - s) ≤ Real.log (Y t 2) - Real.log (Y s 2) ∧
      t - s ≤ (2 * (k + 1) ^ 2 / k) * Real.log (1 / Y s 2) := by
  intro Y hy hvs
  have hk0 : 0 < k := by linarith
  have hK : 0 < k + 1 := by linarith
  have hsm : s ∈ Icc s t := ⟨le_rfl, hst⟩
  have hdom (r : ℝ) (hr : s ≤ r) := normalizedMaxDomain_contains_Ici_of_constraint hc t₀ (hs.trans hr)
  have hv (r : ℝ) (hr : r ∈ Icc s t) : 0 < Y r 2 :=
    normalized_projective_wall_pos (hdom s le_rfl) (hdom r hr.1) (hA s hsm) (hA r hr) 1 hvs
  let z := fun r => Real.log (Y r 2)
  let q := fun r => normalizedProjectiveRate x t₀ r * entranceClockRate (Y r)
  have hz (r : ℝ) (hr : r ∈ Icc s t) : HasDerivAt z (q r) r := by
    have H := normalizedMaxCurve_forward_of_constraint hc (hs.trans hr.1)
    exact hasDerivAt_entranceLog_scaled
      (hasDerivAt_toProjectiveState_normalized H.1 (hA r hr).ne' H.2.1) (hv r hr).ne'
  have hq (r : ℝ) (hr : r ∈ Icc s t) : k / (2 * (k + 1) ^ 2) ≤ q r := by
    have hscale := normalized_entrance_chart_lower hk (hA r hr).ne'
      (normalizedMaxCurve_forward_of_constraint hc (hs.trans hr.1)).2.1 (hy r hr)
    have H := mul_le_mul hscale (entranceRegion_speed hk (hy r hr)).1
      (show 0 ≤ 3 / 4 * k by positivity) (hA r hr).le
    apply le_trans _ H
    apply (div_le_iff₀ (by positivity : 0 < 2 * (k + 1) ^ 2)).mpr
    field_simp
    nlinarith
  have H := (convex_Icc s t).mul_sub_le_image_sub_of_le_deriv (HasDerivAt.continuousOn hz)
    (fun r hr => (hz r (interior_subset hr)).differentiableAt.differentiableWithinAt)
    (fun r hr => by rw [(hz r (interior_subset hr)).deriv]; exact hq r (interior_subset hr))
    s hsm t ⟨hst, le_rfl⟩ hst
  refine ⟨H, ?_⟩
  have hzt : z t ≤ 0 := Real.log_nonpos (hv t ⟨hst, le_rfl⟩).le (hy t ⟨hst, le_rfl⟩).2.2.2.1.2
  have hL : k / (2 * (k + 1) ^ 2) * (t - s) ≤ Real.log (1 / Y s 2) := by
    rw [one_div, Real.log_inv]
    linarith only [H, hzt]
  have hpos : 0 < k / (2 * (k + 1) ^ 2) := by positivity
  have H' := (le_div_iff₀ hpos).mpr (show (t - s) * (k / (2 * (k + 1) ^ 2)) ≤ Real.log (1 / Y s 2) by simpa only [mul_comm] using hL)
  convert! H' using 1
  field_simp

end BianchiIX
