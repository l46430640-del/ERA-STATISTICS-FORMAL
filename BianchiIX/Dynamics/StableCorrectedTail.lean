import BianchiIX.Dynamics.StableCorrectedRemainder

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

/-- A smaller open parameter neighborhood leaves room to restart the same estimate. -/
theorem stableCorrectedApproximation_tail {m c u w T : ℝ}
    (hc : 2 ≤ c) (hm : |m - c| ≤ 1 / 80)
    (hu : |u| ≤ 1 / 200) (hw : |w| ≤ 1 / 200) (hT : 0 ≤ T) :
    |stableBoundaryProjection m u w - stableCorrectedApproximation ![m, u, w] T| ≤
      (1024 * |u| * (|u| + |w|) ^ 3 / (c + 1) ^ 3) * Real.exp (-(3 / 8) * T) := by
  let x := fromProjectiveState (stableBoundaryEntry m u w)
  let Y := stableBoundaryOrbit m u w
  let K := c + 1
  let z := normalizedStableClock x 0 0 c
  have hK : 0 < K := by dsimp [K]; linarith
  have hm' : |m - c| ≤ 1 / 40 := by linarith
  have hglobal := stableBoundaryOrbit_global hc hm' hu hw
  have hsmall : 8 * (|u| + |w|) ^ 2 / K ≤ 1 / 80 := by
    apply (div_le_iff₀ hK).mpr
    have hb : |u| + |w| ≤ 1 / 100 := by linarith
    have hb2 := (sq_le_sq₀ (by positivity : 0 ≤ |u| + |w|) (by norm_num : (0 : ℝ) ≤ 1 / 100)).mpr hb
    dsimp [K]
    nlinarith
  have hMT : |Y T 0 - c| ≤ 1 / 40 := by
    have htri := abs_sub_le (Y T 0) m c
    have hd := (hglobal T hT).2.2.1.trans hsmall
    linarith
  have hUT : |Y T 1| ≤ 1 / 200 := (hglobal T hT).2.2.2.1.trans hu
  have hWT : |Y T 3| ≤ 1 / 200 := (hglobal T hT).2.2.2.2.trans hw
  have H := stableBoundaryProjection_remainder hc hMT hUT hWT
  rw [stableBoundaryProjection_invariant hc hm' hu hw hT] at H
  have hx : stateConstraint x = 1 := fromProjectiveState_constraint (ne_of_gt (stableBoundaryEntry_denom_pos m u w))
  have hapos (t : ℝ) (ht : 0 ≤ t) : 0 < normalizedProjectiveRate x 0 t :=
    lt_of_lt_of_le (by positivity : 0 < 3 / (c + 1) ^ 2) (hglobal t ht).1
  have hdec := (normalized_stable_prefix_estimates hx hc (le_refl 0) hT
    (fun t ht => hapos t ht.1) (fun t ht => (hglobal t ht.1).2.1)).2.1 T ⟨hT, le_rfl⟩
  have hfast : |Y T 1| ≤ |u| * Real.exp (-K / 8 * z T) := by
    have H' := hdec.1
    change |Y T 1| ≤ |Y 0 1| * Real.exp (-K / 8 * z T) at H'
    simpa only [Y, stableBoundaryOrbit_initial, stableBoundaryEntry, Matrix.cons_val_one,
      Matrix.cons_val_zero] using H'
  have hsum : |Y T 1| + |Y T 3| ≤ |u| + |w| :=
    add_le_add (hglobal T hT).2.2.2.1 (hglobal T hT).2.2.2.2
  have hprod := mul_le_mul hfast
    (pow_le_pow_left₀ (by positivity : 0 ≤ |Y T 1| + |Y T 3|) hsum 3)
    (by positivity : 0 ≤ (|Y T 1| + |Y T 3|) ^ 3)
    (by positivity : 0 ≤ |u| * Real.exp (-K / 8 * z T))
  have H' : |stableBoundaryProjection m u w - stableCorrectedApproximation ![m, u, w] T| ≤
      (1024 * |u| * (|u| + |w|) ^ 3 / K ^ 3) * Real.exp (-K / 8 * z T) := by
    apply H.trans
    convert! mul_le_mul_of_nonneg_left hprod (by positivity : 0 ≤ 1024 / K ^ 3) using 1 <;> ring
  have hclock := normalizedStableClock_lower hx hc (le_refl 0) hT (fun t ht => (hglobal t ht.1).1)
  have hclock' : 3 * T ≤ K * z T := by
    have hh : (3 * T) / K ≤ z T := by
      convert! hclock using 1
      simp only [sub_zero]
      ring
    have hh' := (div_le_iff₀ hK).mp hh
    nlinarith only [hh']
  have he : Real.exp (-K / 8 * z T) ≤ Real.exp (-(3 / 8) * T) :=
    Real.exp_le_exp.mpr (by nlinarith only [hclock'])
  exact H'.trans (mul_le_mul_of_nonneg_left he (by positivity))

theorem stableResidualIntegral_tail {m c u w T : ℝ}
    (hc : 2 ≤ c) (hm : |m - c| ≤ 1 / 80)
    (hu : |u| ≤ 1 / 200) (hw : |w| ≤ 1 / 200) (hT : 0 ≤ T) :
    |(stableBoundaryProjection m u w - stableCorrectedPhase m u w) - stableResidualIntegral m u w T| ≤
      (1024 * |u| * (|u| + |w|) ^ 3 / (c + 1) ^ 3) * Real.exp (-(3 / 8) * T) := by
  rw [stableResidualIntegral_eq hc (by linarith : |m - c| ≤ 1 / 40) hu hw hT]
  convert! stableCorrectedApproximation_tail hc hm hu hw hT using 1
  congr 1
  ring

end BianchiIX
