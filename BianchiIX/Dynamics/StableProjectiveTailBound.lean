import BianchiIX.Dynamics.StableProjectiveTail
import BianchiIX.Dynamics.StableCorrectedRemainder

noncomputable section

namespace BianchiIX

/-- The actual projective-time tail retains the strong-wall factor and the fast exponent. -/
theorem stableProjectiveTail_bound {c σ : ℝ} {y : StableState}
    (hc : 2 ≤ c) (hy : y ∈ stableParameterDomain c) (hm : |y 0 - c| ≤ 1 / 80)
    (hσ : 0 ≤ σ) :
    |stableProjectiveTail c σ y| ≤
      (1024 * |y 1| * (|y 1| + |y 2|) ^ 3 / (c + 1) ^ 3) *
        Real.exp (-(c + 1) / 8 * σ) := by
  let T := stableProjectiveCutoff c (y, σ)
  let Y := stableBoundaryOrbit (y 0) (y 1) (y 2)
  let x := fromProjectiveState (stableBoundaryEntry (y 0) (y 1) (y 2))
  have hK : 0 < c + 1 := by linarith
  obtain ⟨ht, he⟩ := stableProjectiveCutoff_spec hc hy hσ
  change 0 ≤ T at ht
  have hg := stableBoundaryOrbit_global hc hy.1.le hy.2.1.le hy.2.2.le
  have hsmall : 8 * (|y 1| + |y 2|) ^ 2 / (c + 1) ≤ 1 / 80 := by
    apply (div_le_iff₀ hK).mpr
    have hb : |y 1| + |y 2| ≤ 1 / 100 := by linarith [hy.2.1, hy.2.2]
    have hb2 := (sq_le_sq₀ (by positivity : 0 ≤ |y 1| + |y 2|)
      (by norm_num : (0 : ℝ) ≤ 1 / 100)).mpr hb
    nlinarith
  have hM : |Y T 0 - c| ≤ 1 / 40 := by
    have htri := abs_sub_le (Y T 0) (y 0) c
    have hd := (hg T ht).2.2.1.trans hsmall
    linarith
  have hU : |Y T 1| ≤ 1 / 200 := (hg T ht).2.2.2.1.trans hy.2.1.le
  have hW : |Y T 3| ≤ 1 / 200 := (hg T ht).2.2.2.2.trans hy.2.2.le
  have HR := stableBoundaryProjection_remainder hc hM hU hW
  rw [stableBoundaryProjection_invariant hc hy.1.le hy.2.1.le hy.2.2.le ht] at HR
  have hx : stateConstraint x = 1 :=
    fromProjectiveState_constraint (stableBoundaryEntry_denom_pos _ _ _).ne'
  have hapos (t : ℝ) (ht : 0 ≤ t) : 0 < normalizedProjectiveRate x 0 t :=
    lt_of_lt_of_le (by positivity : 0 < 3 / (c + 1) ^ 2) (hg t ht).1
  have hdec := (normalized_stable_prefix_estimates hx hc (le_refl 0) ht
    (fun t ht => hapos t ht.1) (fun t ht => (hg t ht.1).2.1)).2.1 T ⟨ht, le_rfl⟩
  have hclock : normalizedStableClock x 0 0 c T = σ :=
    (stableProjectiveClock_eq_normalized hc hy ht).symm.trans he
  have hfast : |Y T 1| ≤ |y 1| * Real.exp (-(c + 1) / 8 * σ) := by
    have H := hdec.1
    rw [hclock] at H
    change |Y T 1| ≤ |Y 0 1| * Real.exp (-(c + 1) / 8 * σ) at H
    simpa only [Y, stableBoundaryOrbit_initial, stableBoundaryEntry, Matrix.cons_val_one,
      Matrix.cons_val_zero] using H
  have hsum : |Y T 1| + |Y T 3| ≤ |y 1| + |y 2| :=
    add_le_add (hg T ht).2.2.2.1 (hg T ht).2.2.2.2
  have hp := mul_le_mul hfast
    (pow_le_pow_left₀ (by positivity : 0 ≤ |Y T 1| + |Y T 3|) hsum 3)
    (by positivity : 0 ≤ (|Y T 1| + |Y T 3|) ^ 3)
    (by positivity : 0 ≤ |y 1| * Real.exp (-(c + 1) / 8 * σ))
  rw [stableProjectiveTail_eq_original hc]
  apply HR.trans
  convert! mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ 1024 / (c + 1) ^ 3) using 1 <;> ring

end BianchiIX
