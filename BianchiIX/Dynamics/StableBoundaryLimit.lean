import BianchiIX.Dynamics.StableBoundaryGlobal
import Mathlib.Topology.MetricSpace.Cauchy

noncomputable section

namespace BianchiIX

open Set Filter MeasureTheory
open scoped Topology

theorem normalizedStableClock_lower {x : NormalizedState} {t₀ s t c : ℝ}
    (hx : stateConstraint x = 1) (hc : 2 ≤ c) (hs : t₀ ≤ s) (hst : s ≤ t)
    (hA : ∀ r ∈ Icc s t, 3 / (c + 1) ^ 2 ≤ normalizedProjectiveRate x t₀ r) :
    3 / (c + 1) * (t - s) ≤ normalizedStableClock x t₀ s c t := by
  have hK : 0 < c + 1 := by linarith
  have hcA : ContinuousOn (normalizedProjectiveRate x t₀) (Icc s t) :=
    (continuousOn_normalizedProjectiveRate x t₀).mono
      (fun r hr => normalizedMaxDomain_contains_Ici_of_constraint hx t₀ (hs.trans hr.1))
  have H := intervalIntegral.integral_mono_on (μ := volume) hst (intervalIntegrable_const (c := 3 / (c + 1) ^ 2))
    (hcA.intervalIntegrable_of_Icc hst) hA
  rw [intervalIntegral.integral_const] at H
  have H' := mul_le_mul_of_nonneg_left H hK.le
  convert! H' using 1
  simp only [smul_eq_mul]
  field_simp

theorem normalized_stable_limit {x : NormalizedState} {t₀ s c : ℝ}
    (hx : stateConstraint x = 1) (hc : 2 ≤ c) (hs : t₀ ≤ s)
    (hA : 0 < normalizedProjectiveRate x t₀ s) :
    let Y := fun r => toProjectiveState (normalizedMaxCurve x t₀ r)
    |Y s 0 - c| ≤ 1 / 40 → |Y s 1| ≤ 1 / 200 → Y s 2 = 0 → |Y s 3| ≤ 1 / 200 →
    ∃ P : ℝ, Tendsto (fun r => Y r 0) atTop (𝓝 P) ∧
      Tendsto (fun r => Y r 1) atTop (𝓝 0) ∧ Tendsto (fun r => Y r 3) atTop (𝓝 0) ∧
      ∀ r ≥ s, |P - Y r 0| ≤ 8 * (|Y r 1| + |Y r 3|) ^ 2 / (c + 1) := by
  intro Y hm hu hv hw
  have hglobal := normalized_stable_global_region hx hc hs hA hm hu hv hw
  have hK : 0 < c + 1 := by linarith
  have hpos : 0 < 3 / (c + 1) ^ 2 := by positivity
  have hclock : Tendsto (normalizedStableClock x t₀ s c) atTop atTop := by
    refine tendsto_atTop_mono' atTop ?_
      (Tendsto.const_mul_atTop (by positivity : 0 < 3 / (c + 1))
        (tendsto_atTop_add_const_right atTop (-s) tendsto_id))
    filter_upwards [eventually_ge_atTop s] with t ht
    simpa only [sub_eq_add_neg, id_eq] using normalizedStableClock_lower hx hc hs ht
      (fun r hr => (hglobal r hr.1).1)
  have hdec (t : ℝ) (ht : s ≤ t) :=
    (normalized_stable_prefix_estimates hx hc hs ht
      (fun r hr => hpos.trans_le (hglobal r hr.1).1)
      (fun r hr => (hglobal r hr.1).2.1)).2.1 t ⟨ht, le_rfl⟩
  have hexp (q : ℝ) (hq : 0 < q) :
      Tendsto (fun t => Real.exp (-q * normalizedStableClock x t₀ s c t)) atTop (𝓝 0) := by
    convert! Real.tendsto_exp_neg_atTop_nhds_zero.comp (Tendsto.const_mul_atTop hq hclock) using 1
    ext t
    congr 1
    ring
  have hUabs : Tendsto (fun t => |Y t 1|) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun _ => abs_nonneg _)) ?_
      (by simpa only [mul_zero] using (hexp ((c + 1) / 8) (by positivity)).const_mul |Y s 1|)
    filter_upwards [eventually_ge_atTop s] with t ht
    simpa only [neg_div] using (hdec t ht).1
  have hWabs : Tendsto (fun t => |Y t 3|) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun _ => abs_nonneg _)) ?_
      (by simpa only [mul_zero] using (hexp (1 / 4) (by norm_num)).const_mul |Y s 3|)
    filter_upwards [eventually_ge_atTop s] with t ht
    exact (hdec t ht).2
  let B := fun r => 8 * (|Y r 1| + |Y r 3|) ^ 2 / (c + 1)
  have hB : Tendsto B atTop (𝓝 0) := by
    simpa only [B, zero_add, zero_pow (by norm_num : 2 ≠ 0), mul_zero, zero_div] using
      (((hUabs.add hWabs).pow 2).const_mul 8).div_const (c + 1)
  have hpair (r : ℝ) (hr : s ≤ r) (t : ℝ) (ht : r ≤ t) : |Y t 0 - Y r 0| ≤ B r :=
    (normalized_stable_prefix_estimates hx hc (hs.trans hr) ht
      (fun q hq => hpos.trans_le (hglobal q (hr.trans hq.1)).1)
      (fun q hq => (hglobal q (hr.trans hq.1)).2.1)).1
  have hC : CauchySeq (fun r : ℝ => Y r 0) := by
    apply Metric.cauchySeq_iff'.mpr
    intro ε hε
    obtain ⟨R, hR⟩ := eventually_atTop.mp (hB.eventually (gt_mem_nhds hε))
    refine ⟨max R s, fun t ht => ?_⟩
    rw [Real.dist_eq]
    exact (hpair (max R s) (le_max_right _ _) t ht).trans_lt (hR _ (le_max_left _ _))
  obtain ⟨P, hP⟩ := cauchy_map_iff_exists_tendsto.mp hC
  refine ⟨P, hP, ?_, ?_, ?_⟩
  · exact tendsto_zero_iff_norm_tendsto_zero.mpr hUabs
  · exact tendsto_zero_iff_norm_tendsto_zero.mpr hWabs
  · intro r hr
    apply le_of_tendsto ((hP.sub_const (Y r 0)).abs)
    filter_upwards [eventually_ge_atTop r] with t ht
    exact hpair r hr t ht

def stableBoundaryEntry (m u w : ℝ) : ProjectiveState := ![m, u, 0, w]

def stableBoundaryOrbit (m u w t : ℝ) : ProjectiveState :=
  toProjectiveState (normalizedMaxCurve (fromProjectiveState (stableBoundaryEntry m u w)) 0 t)

/-- The projection is defined from the exact Einstein orbit in original time. -/
def stableBoundaryProjection (m u w : ℝ) : ℝ :=
  limUnder atTop (fun t => stableBoundaryOrbit m u w t 0)

theorem stableBoundaryEntry_denom_pos (m u w : ℝ) :
    0 < projectiveStateDenom (stableBoundaryEntry m u w) := by
  change 0 < projectiveDenom m u 0 w
  have H : projectiveDenom m u 0 w = 3 + m ^ 2 + (u - w) ^ 2 := by
    unfold projectiveDenom curvature
    ring
  rw [H]
  positivity

theorem stableBoundaryOrbit_initial (m u w : ℝ) :
    stableBoundaryOrbit m u w 0 = stableBoundaryEntry m u w := by
  unfold stableBoundaryOrbit
  rw [normalizedMaxCurve_initial]
  exact toProjectiveState_fromProjectiveState (ne_of_gt (stableBoundaryEntry_denom_pos m u w))

theorem stableBoundaryOrbit_global {m c u w : ℝ}
    (hc : 2 ≤ c) (hm : |m - c| ≤ 1 / 40)
    (hu : |u| ≤ 1 / 200) (hw : |w| ≤ 1 / 200) :
    ∀ t ≥ 0,
      3 / (c + 1) ^ 2 ≤ normalizedProjectiveRate (fromProjectiveState (stableBoundaryEntry m u w)) 0 t ∧
      stableBoundaryRegion c (stableBoundaryOrbit m u w t) ∧
      |stableBoundaryOrbit m u w t 0 - m| ≤ 8 * (|u| + |w|) ^ 2 / (c + 1) ∧
      |stableBoundaryOrbit m u w t 1| ≤ |u| ∧ |stableBoundaryOrbit m u w t 3| ≤ |w| := by
  have hD := stableBoundaryEntry_denom_pos m u w
  have hx := fromProjectiveState_constraint (ne_of_gt hD)
  have hA : 0 < normalizedProjectiveRate (fromProjectiveState (stableBoundaryEntry m u w)) 0 0 := by
    unfold normalizedProjectiveRate
    rw [normalizedMaxCurve_initial]
    exact fromProjectiveState_clock_pos hD
  have hi := stableBoundaryOrbit_initial m u w
  have H := normalized_stable_global_region hx hc (le_refl 0) hA
  change |stableBoundaryOrbit m u w 0 0 - c| ≤ 1 / 40 →
    |stableBoundaryOrbit m u w 0 1| ≤ 1 / 200 → stableBoundaryOrbit m u w 0 2 = 0 →
    |stableBoundaryOrbit m u w 0 3| ≤ 1 / 200 → _ at H
  have H' := H (by simpa [hi, stableBoundaryEntry] using hm)
    (by simpa [hi, stableBoundaryEntry] using hu) (by simp [hi, stableBoundaryEntry])
    (by simpa [hi, stableBoundaryEntry] using hw)
  change ∀ t ≥ 0, _ ∧ stableBoundaryRegion c (stableBoundaryOrbit m u w t) ∧
    |stableBoundaryOrbit m u w t 0 - stableBoundaryOrbit m u w 0 0| ≤
      8 * (|stableBoundaryOrbit m u w 0 1| + |stableBoundaryOrbit m u w 0 3|) ^ 2 / (c + 1) ∧
    |stableBoundaryOrbit m u w t 1| ≤ |stableBoundaryOrbit m u w 0 1| ∧
    |stableBoundaryOrbit m u w t 3| ≤ |stableBoundaryOrbit m u w 0 3| at H'
  simpa [hi, stableBoundaryEntry] using H'

theorem stableBoundaryProjection_exists {m c u w : ℝ}
    (hc : 2 ≤ c) (hm : |m - c| ≤ 1 / 40)
    (hu : |u| ≤ 1 / 200) (hw : |w| ≤ 1 / 200) :
    Tendsto (fun t => stableBoundaryOrbit m u w t 0) atTop (𝓝 (stableBoundaryProjection m u w)) ∧
    Tendsto (fun t => stableBoundaryOrbit m u w t 1) atTop (𝓝 0) ∧
    Tendsto (fun t => stableBoundaryOrbit m u w t 3) atTop (𝓝 0) ∧
    (∀ t ≥ 0, |stableBoundaryProjection m u w - stableBoundaryOrbit m u w t 0| ≤
      8 * (|stableBoundaryOrbit m u w t 1| + |stableBoundaryOrbit m u w t 3|) ^ 2 / (c + 1)) ∧
    |stableBoundaryProjection m u w - m| ≤ 8 * (|u| + |w|) ^ 2 / (c + 1) := by
  let x := fromProjectiveState (stableBoundaryEntry m u w)
  have hD := stableBoundaryEntry_denom_pos m u w
  have hx : stateConstraint x = 1 := fromProjectiveState_constraint (ne_of_gt hD)
  have hA : 0 < normalizedProjectiveRate x 0 0 := by
    unfold normalizedProjectiveRate
    rw [normalizedMaxCurve_initial]
    exact fromProjectiveState_clock_pos hD
  have hi := stableBoundaryOrbit_initial m u w
  have H := normalized_stable_limit hx hc (le_refl 0) hA
  change |stableBoundaryOrbit m u w 0 0 - c| ≤ 1 / 40 →
    |stableBoundaryOrbit m u w 0 1| ≤ 1 / 200 → stableBoundaryOrbit m u w 0 2 = 0 →
    |stableBoundaryOrbit m u w 0 3| ≤ 1 / 200 → _ at H
  obtain ⟨P, hP, hU, hW, htail⟩ := H (by simpa [hi, stableBoundaryEntry] using hm)
    (by simpa [hi, stableBoundaryEntry] using hu) (by simp [hi, stableBoundaryEntry])
    (by simpa [hi, stableBoundaryEntry] using hw)
  have heq : stableBoundaryProjection m u w = P := hP.limUnder_eq
  rw [heq]
  refine ⟨hP, hU, hW, htail, ?_⟩
  have H0 := htail 0 le_rfl
  change |P - stableBoundaryOrbit m u w 0 0| ≤
    8 * (|stableBoundaryOrbit m u w 0 1| + |stableBoundaryOrbit m u w 0 3|) ^ 2 / (c + 1) at H0
  simpa [hi, stableBoundaryEntry] using H0

theorem stableBoundaryProjection_zero {m : ℝ} (hm : 2 ≤ m) :
    stableBoundaryProjection m 0 0 = m := by
  have H := (stableBoundaryProjection_exists hm (by simp : |m - m| ≤ (1 : ℝ) / 40)
    (by norm_num : |(0 : ℝ)| ≤ 1 / 200) (by norm_num : |(0 : ℝ)| ≤ 1 / 200)).2.2.2.2
  have H0 : |stableBoundaryProjection m 0 0 - m| ≤ 0 := by simpa using H
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm H0 (abs_nonneg _)))

end BianchiIX
