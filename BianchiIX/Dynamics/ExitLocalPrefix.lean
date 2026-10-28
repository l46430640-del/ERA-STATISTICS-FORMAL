import BianchiIX.Dynamics.ExitPhysicalRegion
import BianchiIX.Dynamics.CoreEntry

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

theorem normalized_exit_local_prefix {x : NormalizedState} {t₀ s h : ℝ}
    (hc : stateConstraint x = 1) (hh : 0 < h) (hs : t₀ ≤ s)
    (hA : 0 < 1 + normalizedMaxCurve x t₀ s 0) :
    let y := toProjectiveState (normalizedMaxCurve x t₀ s)
    y 0 < 0 → (7 / 4 < coreRadius (y 0) (y 2) ∧ coreRadius (y 0) (y 2) < 17 / 4) →
    |y 1| < 1 / 100 → (h < y 2 ∧ y 2 ≤ 1) → |y 3| < 1 / 100 →
    ∃ r > s, ∀ u ∈ Icc s r, 1 / 16 < 1 + normalizedMaxCurve x t₀ u 0 ∧
      exitPhysicalRegion h (toProjectiveState (normalizedMaxCurve x t₀ u)) := by
  intro y hm hR hu hv hw
  let β := fun u => toProjectiveState (normalizedMaxCurve x t₀ u)
  have hregion : exitPhysicalRegion h y := ⟨hm.le, ⟨hR.1.le, hR.2.le⟩, hu.le, ⟨hv.1.le, hv.2⟩, hw.le⟩
  have hactual := normalizedMaxCurve_forward_of_constraint hc hs
  have hsol : HasDerivAt β ((1 + normalizedMaxCurve x t₀ s 0) • projectiveField (β s)) s :=
    hasDerivAt_toProjectiveState_normalized hactual.1 (ne_of_gt hA) hactual.2.1
  have hcoord (i : Fin 4) := (hasDerivAt_pi.mp hsol i).continuousAt
  have hAc : ContinuousAt (fun u => 1 + normalizedMaxCurve x t₀ u 0) s :=
    continuousAt_const.add (hasDerivAt_pi.mp hactual.1 0).continuousAt
  have hRc : ContinuousAt (fun u => coreRadius (β u 0) (β u 2)) s := by
    unfold coreRadius coreEnergy
    fun_prop
  have hmargin : 1 / 16 < 1 + normalizedMaxCurve x t₀ s 0 :=
    lt_of_lt_of_le (by norm_num) (normalized_exit_chart_lower hh (ne_of_gt hA) hactual.2.1 hregion)
  have hD : 0 < exitClockRate (β s) := by
    have H := exitPhysicalRegion_clock hh hregion
    change 1 / 2 ≤ exitClockRate (β s) at H
    linarith only [H]
  have hVbound : ∀ᶠ u in 𝓝[>] s, β u 2 < 1 := by
    apply eventually_lt_bound_of_deriv_inward (hasDerivAt_pi.mp hsol 2) hv.2
    intro hcap
    change (1 + normalizedMaxCurve x t₀ s 0) * activeVelocity (β s 0) (β s 1) (β s 2) (β s 3) < 0
    have heq : activeVelocity (β s 0) (β s 1) (β s 2) (β s 3) = -exitClockRate (β s) * β s 2 := by
      dsimp only [activeVelocity, exitClockRate]
      ring
    rw [heq, hcap, mul_one]
    exact mul_neg_of_pos_of_neg hA (neg_neg_of_pos hD)
  have H : ∀ᶠ u in 𝓝[>] s, 1 / 16 < 1 + normalizedMaxCurve x t₀ u 0 ∧ exitPhysicalRegion h (β u) := by
    filter_upwards [(hAc.eventually (isOpen_Ioi.mem_nhds hmargin)).filter_mono nhdsWithin_le_nhds,
      ((hcoord 0).eventually (isOpen_Iio.mem_nhds hm)).filter_mono nhdsWithin_le_nhds,
      (hRc.eventually (Ioo_mem_nhds hR.1 hR.2)).filter_mono nhdsWithin_le_nhds,
      ((hcoord 1).abs.eventually (isOpen_Iio.mem_nhds hu)).filter_mono nhdsWithin_le_nhds,
      ((hcoord 2).eventually (isOpen_Ioi.mem_nhds hv.1)).filter_mono nhdsWithin_le_nhds,
      ((hcoord 3).abs.eventually (isOpen_Iio.mem_nhds hw)).filter_mono nhdsWithin_le_nhds, hVbound]
      with u hAu hmu hRu huu hvu hwu hVu
    exact ⟨hAu, hmu.le, ⟨hRu.1.le, hRu.2.le⟩, huu.le, ⟨hvu.le, hVu.le⟩, hwu.le⟩
  obtain ⟨r, hr, hsub⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp H
  refine ⟨r, hr, ?_⟩
  intro u hu
  rcases eq_or_lt_of_le hu.1 with heq | hlt
  · subst u
    exact ⟨hmargin, hregion⟩
  · exact hsub ⟨hlt, hu.2⟩

end BianchiIX
