import BianchiIX.Algebra.StableResidualBounds
import BianchiIX.Dynamics.StableCorrectedFlow

noncomputable section

namespace BianchiIX

open Set Filter MeasureTheory
open scoped Topology

theorem stableResidualIntegral_bound {m c u w T : ℝ}
    (hc : 2 ≤ c) (hm : |m - c| ≤ 1 / 40)
    (hu : |u| ≤ 1 / 200) (hw : |w| ≤ 1 / 200) (hT : 0 ≤ T) :
    |stableResidualIntegral m u w T| ≤ 1024 * |u| * (|u| + |w|) ^ 3 / (c + 1) ^ 3 := by
  let x := fromProjectiveState (stableBoundaryEntry m u w)
  let Y := stableBoundaryOrbit m u w
  let a := normalizedProjectiveRate x 0
  let K := c + 1
  let z := normalizedStableClock x 0 0 c
  let C := 128 * |u| * (|u| + |w|) ^ 3 / K ^ 2
  let e := fun t => Real.exp (-K / 8 * z t)
  let B := fun t => C * ((K * a t) * e t)
  have hK : 0 < K := by dsimp [K]; linarith
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hglobal := stableBoundaryOrbit_global hc hm hu hw
  have hx : stateConstraint x = 1 := fromProjectiveState_constraint (ne_of_gt (stableBoundaryEntry_denom_pos m u w))
  have hdom (t : ℝ) (ht : 0 ≤ t) : t ∈ normalizedMaxDomain x 0 :=
    normalizedMaxDomain_contains_Ici_of_constraint hx 0 ht
  have hapos (t : ℝ) (ht : 0 ≤ t) : 0 < a t :=
    lt_of_lt_of_le (by positivity : 0 < 3 / (c + 1) ^ 2) (hglobal t ht).1
  have hY (t : ℝ) (ht : 0 ≤ t) := hasDerivAt_stableBoundaryOrbit hc hm hu hw ht
  have hM (t : ℝ) (ht : 0 ≤ t) : 1 < Y t 0 := by
    have hl := (abs_le.mp (hglobal t ht).2.1.1).1
    linarith
  have hd (t : ℝ) (ht : 0 ≤ t) := hasDerivAt_stableCorrectedPhase_scaled
    (hY t ht) (hM t ht) (hglobal t ht).2.1.2.2.1
  have hz (t : ℝ) (ht : t ∈ Icc 0 T) : HasDerivAt z (K * a t) t :=
    hasDerivAt_normalizedStableClock (hdom 0 le_rfl) (hdom t ht.1)
  have ha : ContinuousOn a (Icc 0 T) := (continuousOn_normalizedProjectiveRate _ _).mono
    (fun t ht => hdom t ht.1)
  have he : ContinuousOn e (Icc 0 T) := Real.continuous_exp.comp_continuousOn
    ((HasDerivAt.continuousOn hz).const_mul (-K / 8))
  have hB : ContinuousOn B (Icc 0 T) := (((ha.const_mul K).mul he).const_mul C)
  have hfast (t : ℝ) (ht : t ∈ Icc 0 T) : |Y t 1| ≤ |u| * e t := by
    have H := (normalized_stable_prefix_estimates hx hc (le_refl 0) hT
      (fun r hr => hapos r hr.1) (fun r hr => (hglobal r hr.1).2.1)).2.1 t ht
    have H' := H.1
    change |Y t 1| ≤ |Y 0 1| * e t at H'
    simpa only [Y, stableBoundaryOrbit_initial, stableBoundaryEntry, Matrix.cons_val_one,
      Matrix.cons_val_zero] using H'
  have hbound (t : ℝ) (ht : t ∈ Icc 0 T) :
      |a t * stableCorrectedResidual (Y t 0) (Y t 1) (Y t 3)| ≤ B t := by
    have hsum : |Y t 1| + |Y t 3| ≤ |u| + |w| :=
      add_le_add (hglobal t ht.1).2.2.2.1 (hglobal t ht.1).2.2.2.2
    have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ |Y t 1| + |Y t 3|) hsum 3
    have hprod := mul_le_mul (hfast t ht) hpow (by positivity : 0 ≤ (|Y t 1| + |Y t 3|) ^ 3)
      (by positivity : 0 ≤ |u| * e t)
    have hR := stableCorrectedResidual_band_bound (u := Y t 1) (w := Y t 3) hc (hglobal t ht.1).2.1.1
    have hR' := hR.trans (by
      convert! mul_le_mul_of_nonneg_left hprod (by positivity : 0 ≤ 128 / K) using 1
      ring)
    rw [abs_mul, abs_of_pos (hapos t ht.1)]
    apply (mul_le_mul_of_nonneg_left hR' (hapos t ht.1).le).trans_eq
    dsimp [B, C]
    field_simp
  have H := abs_sub_le_integral_bound hT (fun t ht => hd t ht.1) hB hbound
  have heq := stableResidualIntegral_eq hc hm hu hw hT
  have hinit : stableCorrectedPhase (Y 0 0) (Y 0 1) (Y 0 3) = stableCorrectedPhase m u w := by
    simp [Y, stableBoundaryOrbit_initial, stableBoundaryEntry]
  change |stableCorrectedApproximation ![m, u, w] T - stableCorrectedPhase (Y 0 0) (Y 0 1) (Y 0 3)| ≤ _ at H
  rw [hinit, ← heq] at H
  have hz0 : z 0 = 0 := by simp [z, normalizedStableClock, integralClock_initial]
  have HI : (∫ t in 0..T, (K * a t) * e t) ≤ 1 / (K / 8) := by
    simpa only [hz0, sub_zero, neg_div, e] using
      integral_clock_exp_decay_le hT (by positivity : 0 < K / 8) hz (ha.const_mul K)
  change |stableResidualIntegral m u w T| ≤ ∫ t in 0..T, C * ((K * a t) * e t) at H
  rw [intervalIntegral.integral_const_mul] at H
  apply H.trans ((mul_le_mul_of_nonneg_left HI hC).trans_eq ?_)
  dsimp [C, K]
  field_simp
  ring

theorem stableBoundaryProjection_remainder {m c u w : ℝ}
    (hc : 2 ≤ c) (hm : |m - c| ≤ 1 / 40)
    (hu : |u| ≤ 1 / 200) (hw : |w| ≤ 1 / 200) :
    |stableBoundaryProjection m u w - stableCorrectedPhase m u w| ≤
      1024 * |u| * (|u| + |w|) ^ 3 / (c + 1) ^ 3 := by
  apply le_of_tendsto (stableResidualIntegral_tendsto hc hm hu hw).abs
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
  exact stableResidualIntegral_bound hc hm hu hw hT

theorem stableBoundaryProjection_weak {m c w : ℝ}
    (hc : 2 ≤ c) (hm : |m - c| ≤ 1 / 40) (hw : |w| ≤ 1 / 200) :
    stableBoundaryProjection m 0 w = stableWeakRadius m w - 1 := by
  have H := stableBoundaryProjection_remainder hc hm (by norm_num : |(0 : ℝ)| ≤ 1 / 200) hw
  have H0 : |stableBoundaryProjection m 0 w - (stableWeakRadius m w - 1)| ≤ 0 := by
    simpa [stableCorrectedPhase] using H
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm H0 (abs_nonneg _)))

end BianchiIX
