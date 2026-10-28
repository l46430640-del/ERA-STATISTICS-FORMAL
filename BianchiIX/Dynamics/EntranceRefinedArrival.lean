import BianchiIX.Dynamics.EntranceArcDecay
import BianchiIX.Dynamics.EntranceTime

noncomputable section

namespace BianchiIX

open Set

theorem entrance_arc_prefactor_bound {k u w : ℝ} (hk : 7 / 4 ≤ k)
    (hu : 0 ≤ u ∧ u ≤ 1 / 10000) (hw : 0 ≤ w ∧ w ≤ 1 / 10000) :
    Real.exp ((2 * w + 3 * u ^ 2) / k) ≤ Real.exp (1 / 1000) := by
  have hk0 : 0 < k := by linarith
  apply Real.exp_le_exp.mpr
  apply (div_le_iff₀ hk0).mpr
  have hu2 := pow_le_pow_left₀ hu.1 hu.2 2
  nlinarith only [hw.2, hu2, hk]

theorem exists_normalized_entrance_refined_arrival {x : NormalizedState} {t₀ s k : ℝ}
    (hc : stateConstraint x = 1) (hk : 7 / 4 ≤ k) (hs : t₀ ≤ s)
    (hA : 0 < normalizedProjectiveRate x t₀ s) :
    let Y := fun r => toProjectiveState (normalizedMaxCurve x t₀ r)
    1 ≤ Y s 0 → coreRadius (Y s 0) (Y s 2) = k →
    (0 ≤ Y s 1 ∧ Y s 1 ≤ 1 / 10000) → (0 < Y s 2 ∧ Y s 2 < 1) →
    (0 ≤ Y s 3 ∧ Y s 3 ≤ 1 / 10000) →
    ∃ t > s, Y t 2 = 1 ∧ (∀ r ∈ Ico s t, Y r 2 < 1) ∧
      (∀ r ∈ Icc s t, 1 / (2 * (k + 1) ^ 2) ≤ normalizedProjectiveRate x t₀ r ∧ entranceRegion k (Y r)) ∧
      (∀ r ∈ Icc s t, Y r 1 ≤ Y s 1 * Real.exp ((2 * Y s 3 + 3 * (Y s 1) ^ 2) / k) *
        Real.exp (-(1 + 99 * k / 200) * (Real.log (Y r 2) - Real.log (Y s 2)))) ∧
      Y t 1 ≤ Y s 1 * Real.exp ((2 * Y s 3 + 3 * (Y s 1) ^ 2) / k) * (Y s 2) ^ (1 + 99 * k / 200) := by
  intro Y hm hR hu hv hw
  obtain ⟨t, hst, hhit, hbefore, hregion, _⟩ := exists_normalized_entrance_first_arrival hc hk hs hA hm hR hu hv hw
  change Y t 2 = 1 at hhit
  have hK : 0 < k + 1 := by linarith
  have hpos : 0 < 1 / (2 * (k + 1) ^ 2) := by positivity
  have hAp (r : ℝ) (hr : r ∈ Icc s t) := hpos.trans_le (hregion r hr).1
  have hbound (r : ℝ) (hr : r ∈ Icc s t) :
      Y r 1 ≤ Y s 1 * Real.exp ((2 * Y s 3 + 3 * (Y s 1) ^ 2) / k) *
        Real.exp (-(1 + 99 * k / 200) * (Real.log (Y r 2) - Real.log (Y s 2))) := by
    have hsub : Icc s r ⊆ Icc s t := fun b hb => ⟨hb.1, hb.2.trans hr.2⟩
    exact normalized_entrance_arc_decay hc hk hs hr.1 (fun b hb => hAp b (hsub hb))
      (fun b hb => (hregion b (hsub hb)).2) hv.1
  refine ⟨t, hst, hhit, hbefore, hregion, hbound, ?_⟩
  have H := hbound t ⟨hst.le, le_rfl⟩
  rw [hhit, Real.log_one, zero_sub, neg_mul_neg] at H
  rw [Real.rpow_def_of_pos hv.1]
  convert! H using 1
  congr 2
  ring

theorem exists_entrance_refined_first_arrival {k m u v w : ℝ} (hk : 7 / 4 ≤ k)
    (hm : 1 ≤ m) (hR : coreRadius m v = k) (hu : 0 ≤ u ∧ u ≤ 1 / 10000)
    (hv : 0 < v ∧ v < 1) (hw : 0 ≤ w ∧ w ≤ 1 / 10000) :
    let x := fromProjectiveState ![m, u, v, w]
    let Y := fun r => toProjectiveState (normalizedMaxCurve x 0 r)
    ∃ T > (0 : ℝ), Y T 2 = 1 ∧ (∀ r ∈ Ico 0 T, Y r 2 < 1) ∧
      (Real.log (1 / v) / (2 * k) ≤ integralClock (normalizedProjectiveRate x 0) 0 T ∧
        integralClock (normalizedProjectiveRate x 0) 0 T ≤ 2 * Real.log (1 / v) / k) ∧
      (∀ r ∈ Icc 0 T, entranceRegion k (Y r) ∧
        Y r 1 ≤ u * Real.exp ((2 * w + 3 * u ^ 2) / k) *
          Real.exp (-(1 + 99 * k / 200) * (Real.log (Y r 2) - Real.log v))) ∧
      Y T 1 ≤ u * Real.exp ((2 * w + 3 * u ^ 2) / k) * v ^ (1 + 99 * k / 200) := by
  intro x Y
  have hrad : |coreRadius m v - k| ≤ k / 100 := by rw [hR, sub_self, abs_zero]; linarith
  have hD : 0 < projectiveStateDenom ![m, u, v, w] :=
    (entrance_denom_bounds hk (entrance_phase_bounds hk hm hrad ⟨hv.1.le, hv.2.le⟩) hu ⟨hv.1.le, hv.2.le⟩ hw).1
  have hc : stateConstraint x = 1 := fromProjectiveState_constraint hD.ne'
  have hinit : toProjectiveState (normalizedMaxCurve x 0 0) = ![m, u, v, w] := by
    rw [normalizedMaxCurve_initial]
    exact toProjectiveState_fromProjectiveState hD.ne'
  have hA : 0 < normalizedProjectiveRate x 0 0 := by
    unfold normalizedProjectiveRate
    rw [normalizedMaxCurve_initial]
    exact fromProjectiveState_clock_pos hD
  obtain ⟨T, hT, hhit, hbefore, hregion, hbound, hout⟩ := exists_normalized_entrance_refined_arrival hc hk le_rfl hA
    (by simpa [hinit] using hm) (by simpa [hinit] using hR) (by simpa [hinit] using hu)
    (by simpa [hinit] using hv) (by simpa [hinit] using hw)
  have hK : 0 < k + 1 := by linarith
  have hpos : 0 < 1 / (2 * (k + 1) ^ 2) := by positivity
  have hAp (r : ℝ) (hr : r ∈ Icc 0 T) := hpos.trans_le (hregion r hr).1
  have htime := normalized_entrance_projective_time hc hk le_rfl hT.le hAp
    (fun r hr => (hregion r hr).2) (by simpa [hinit] using hv.1) hhit
  refine ⟨T, hT, hhit, hbefore, ?_, ?_, ?_⟩
  · simpa [hinit] using htime
  · intro r hr
    exact ⟨(hregion r hr).2, by simpa [hinit] using hbound r hr⟩
  · simpa [hinit] using hout

end BianchiIX
