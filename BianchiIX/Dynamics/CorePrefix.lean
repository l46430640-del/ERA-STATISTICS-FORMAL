import BianchiIX.Analysis.IntervalNeighborhood
import BianchiIX.Dynamics.CoreRadiusDrift
import BianchiIX.Dynamics.CoreResidence
import BianchiIX.Dynamics.CoreAngleClock

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

/-- Pointwise regularity on a closed prefix supplies the open interval needed by the inverse clock. -/
theorem exists_normalized_core_regular_interval {x : NormalizedState} {t₀ s t : ℝ}
    (hst : s ≤ t) (hdom : Icc s t ⊆ normalizedMaxDomain x t₀)
    (hA : ∀ u ∈ Icc s t, 0 < 1 + normalizedMaxCurve x t₀ u 0)
    (hv : ∀ u ∈ Icc s t, 0 < toProjectiveState (normalizedMaxCurve x t₀ u) 2)
    (hd : ∀ u ∈ Icc s t, let y := toProjectiveState (normalizedMaxCurve x t₀ u)
      0 < coreClockFactor (coreRadius (y 0) (y 2)) (y 1) (y 3)) :
    ∃ l r : ℝ, l < s ∧ t < r ∧ ∀ u ∈ Ioo l r,
      u ∈ normalizedMaxDomain x t₀ ∧ 0 < 1 + normalizedMaxCurve x t₀ u 0 ∧
      0 < toProjectiveState (normalizedMaxCurve x t₀ u) 2 ∧
      let y := toProjectiveState (normalizedMaxCurve x t₀ u)
      0 < coreClockFactor (coreRadius (y 0) (y 2)) (y 1) (y 3) := by
  apply exists_Ioo_covering_of_eventually hst
  intro u hu
  let β := fun v => toProjectiveState (normalizedMaxCurve x t₀ v)
  have hα := (hasDerivAt_normalizedMaxCurve (hdom hu)).continuousAt
  have hAc : ContinuousAt (fun v => 1 + normalizedMaxCurve x t₀ v 0) u :=
    continuousAt_const.add ((continuous_apply 0).continuousAt.comp hα)
  have hβ : ContinuousAt β u :=
    (contDiffAt_toProjectiveState 1 (ne_of_gt (hA u hu))).continuousAt.comp hα
  have hcoord (i : Fin 4) : ContinuousAt (fun v => β v i) u :=
    (continuous_apply i).continuousAt.comp hβ
  have hR : ContinuousAt (fun v => coreRadius (β v 0) (β v 2)) u := by
    unfold coreRadius coreEnergy
    exact (((hcoord 0).sub continuousAt_const).pow 2 |>.add ((hcoord 2).pow 2)).sqrt
  have hdc : ContinuousAt (fun v => coreClockFactor (coreRadius (β v 0) (β v 2)) (β v 1) (β v 3)) u :=
    continuousAt_const.sub (((hcoord 1).sub (hcoord 3)).pow 2 |>.div (hR.pow 2)
      (pow_ne_zero 2 (ne_of_gt (coreRadius_pos (hv u hu)))))
  have hmem : ∀ᶠ v in 𝓝 u, v ∈ normalizedMaxDomain x t₀ :=
    (isOpen_normalizedMaxDomain x t₀).mem_nhds (hdom hu)
  exact hmem.and
    ((hAc.eventually (isOpen_Ioi.mem_nhds (hA u hu))).and
      (((hcoord 2).eventually (isOpen_Ioi.mem_nhds (hv u hu))).and
        (hdc.eventually (isOpen_Ioi.mem_nhds (hd u hu)))))

/-- The strict energy improvement holds on actual closed Einstein-flow prefixes, with no extra clock assumptions. -/
theorem normalized_core_energy_band_improves {x : NormalizedState} {t₀ s t k : ℝ}
    (hc : stateConstraint x = 1) (hk : 6 ≤ k) (hs : t₀ ≤ s) (hst : s ≤ t)
    (hA : ∀ u ∈ Icc s t, 0 < 1 + normalizedMaxCurve x t₀ u 0) :
    let β := fun u => toProjectiveState (normalizedMaxCurve x t₀ u)
    coreRadius (β s 0) (β s 2) = k → β s 2 = 1 →
    (∀ u ∈ Icc s t, |coreRadius (β u 0) (β u 2) ^ 2 - k ^ 2| ≤ 1 / 8) →
    (∀ u ∈ Icc s t, 1 ≤ β u 2) →
    (∀ u ∈ Icc s t, 0 ≤ β u 1 ∧ β u 1 ≤ (1 / 10000) / k) →
    (∀ u ∈ Icc s t, 0 ≤ β u 2 * β u 3 ∧ β u 2 * β u 3 ≤ (1 / 10000) / k) →
    |coreRadius (β t 0) (β t 2) - k| ≤ 16 / k * (β s 1 + (β s 3) ^ 2) ∧
      |coreRadius (β t 0) (β t 2) ^ 2 - k ^ 2| < 1 / 16 := by
  intro β hinit hvs hband hv hu hp
  have hsm : s ∈ Icc s t := ⟨le_rfl, hst⟩
  have htm : t ∈ Icc s t := ⟨hst, le_rfl⟩
  have hdom (u : ℝ) (hh : u ∈ Icc s t) : u ∈ normalizedMaxDomain x t₀ :=
    normalizedMaxDomain_contains_Ici_of_constraint hc t₀ (hs.trans hh.1)
  have hvpos (u : ℝ) (hh : u ∈ Icc s t) : 0 < β u 2 := lt_of_lt_of_le zero_lt_one (hv u hh)
  have hr (u : ℝ) (hh : u ∈ Icc s t) :
      99 / 100 * k ≤ coreRadius (β u 0) (β u 2) ∧ coreRadius (β u 0) (β u 2) ≤ 101 / 100 * k :=
    coreBootstrap_radius_closed hk (coreRadius_pos (hvpos u hh)).le (hband u hh)
  have hw (u : ℝ) (hh : u ∈ Icc s t) : 0 ≤ β u 3 ∧ β u 3 ≤ (1 / 10000) / k := by
    have hnonneg : 0 ≤ β u 3 := (mul_nonneg_iff_of_pos_left (hvpos u hh)).mp (hp u hh).1
    exact ⟨hnonneg, (le_mul_of_one_le_left hnonneg (hv u hh)).trans (hp u hh).2⟩
  have hd (u : ℝ) (hh : u ∈ Icc s t) :
      0 < coreClockFactor (coreRadius (β u 0) (β u 2)) (β u 1) (β u 3) :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 999 / 1000)
      (coreBootstrap_clock_bounds hk (hr u hh).1 (hu u hh) (hw u hh)).1
  obtain ⟨l, r, hls, htr, hregular⟩ := exists_normalized_core_regular_interval hst
    (fun _ hh => hdom _ hh) hA hvpos hd
  have hcover : Icc s t ⊆ Ioo l r := fun u hh => ⟨hls.trans_le hh.1, hh.2.trans_lt htr⟩
  have hsI := hcover hsm
  have htI := hcover htm
  obtain ⟨e, hsrc, heq, htarget, hzero, hinv0, hmono, hflow⟩ :=
    exists_normalized_coreAngle_reparametrization (convex_Ioo l r) isOpen_Ioo hsI
      (fun u hh => (hregular u hh).1) hc
      (fun u hh => (hregular u hh).2.1) (fun u hh => (hregular u hh).2.2.1)
      (fun u hh => (hregular u hh).2.2.2)
  have htE : t ∈ e.source := by rwa [hsrc]
  have hes : e s = 0 := by rw [heq s hsI]; exact sub_self _
  have hbt : 0 ≤ e t := by simpa only [hes] using hmono.monotoneOn hsI htI hst
  have hzt (z : ℝ) (hz : z ∈ Icc 0 (e t)) : z ∈ e.target :=
    htarget.ordConnected.out hzero (e.map_source htE) hz
  have hinv (z : ℝ) (hz : z ∈ Icc 0 (e t)) : e.symm z ∈ Icc s t := by
    have hzT := hzt z hz
    have hxI : e.symm z ∈ Ioo l r := by rw [← hsrc]; exact e.map_target hzT
    constructor
    · apply (hmono.le_iff_le hsI hxI).mp
      rw [hes, e.right_inv hzT]
      exact hz.1
    · apply (hmono.le_iff_le hxI htI).mp
      rw [e.right_inv hzT]
      exact hz.2
  let Y := fun z => toCoreAngleState (β (e.symm z))
  let z₀ := coreAngle (β s 0) (β s 2)
  have hY (z : ℝ) (hz : z ∈ Icc 0 (e t)) : HasDerivAt Y (coreAngleField (z + z₀) (Y z)) z :=
    (hflow z (hzt z hz)).2.1
  have hvY (z : ℝ) (hz : z ∈ Icc 0 (e t)) : Y z 0 / Real.cosh (z + z₀) = β (e.symm z) 2 := by
    have he := (hflow z (hzt z hz)).1
    change coreRadius (β (e.symm z) 0) (β (e.symm z) 2) / Real.cosh (z + z₀) = _
    rw [← he]
    exact (coreAngle_coordinates (hvpos _ (hinv z hz))).1
  have hY0 : Y 0 0 = k := by change coreRadius (β (e.symm 0) 0) (β (e.symm 0) 2) = k; rwa [hinv0]
  have hentry : Real.cosh (0 + z₀) = k := by
    simp only [zero_add]
    dsimp [z₀]
    rw [cosh_coreAngle (hvpos s hsm), hinit, hvs, div_one]
  have H := coreAngle_radius_drift_shifted hbt hk hY hY0 hentry
    (fun z hz => hr _ (hinv z hz))
    (fun z hz => by rw [hvY z hz]; exact hv _ (hinv z hz))
    (fun z hz => hu _ (hinv z hz)) (fun z hz => hp _ (hinv z hz))
  have hinvt : e.symm (e t) = t := e.left_inv htE
  change |coreRadius (β (e.symm (e t)) 0) (β (e.symm (e t)) 2) - k| ≤
    16 / k * (β (e.symm 0) 1 + (β (e.symm 0) 2 * β (e.symm 0) 3) ^ 2) at H
  rw [hinvt, hinv0, hvs, one_mul] at H
  exact ⟨H, core_radius_energy_improvement hk (coreRadius_pos (hvpos t htm)).le (hr t htm).2
    (hu s hsm) (hw s hsm) H⟩

end BianchiIX
