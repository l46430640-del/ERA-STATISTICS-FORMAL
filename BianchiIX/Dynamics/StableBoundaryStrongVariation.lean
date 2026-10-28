import BianchiIX.Dynamics.StableBoundaryStrongCoefficients
import BianchiIX.Dynamics.StableBoundaryForcedVariation

noncomputable section

namespace BianchiIX

open Set

theorem stableRescaledDifferential_strong_decay {y : StableState} {c s : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 40)
    (hu : |y 1| ≤ 1 / 200) (hw : |y 2| ≤ 1 / 200) (hs : 0 ≤ s) (v : StableState) :
    |stableRescaledDifferential (c + 1) y s v 1| ≤
      (|v 1| + 512 * |y 1| * Real.exp (512 * (|y 1| + |y 2|)) * ‖v‖ / (c + 1)) *
        Real.exp (-3 * (c + 1) / 16 * s) := by
  let K := c + 1
  let M := Real.exp (512 * (|y 1| + |y 2|)) * ‖v‖
  let Y := stableRescaledFlow K y
  let J := fun r => stableRescaledDifferential K y r v
  let F : ℝ → (Unit → ℝ) := fun r _ => J r 1
  let A : ℝ → Matrix Unit Unit ℝ := fun r _ _ => K * stableOriginalJacobian (Y r) 1 1
  let q : ℝ → (Unit → ℝ) := fun r _ => K * stableOriginalJacobian (Y r) 1 0 * J r 0 +
    K * stableOriginalJacobian (Y r) 1 2 * J r 2
  have hK : 0 < K := by dsimp [K]; linarith
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hF (r : ℝ) (hr : r ∈ Icc 0 s) : HasDerivAt F ((A r).mulVec (F r) + q r) r := by
    apply hasDerivAt_pi.mpr
    intro i
    apply (hasDerivAt_pi.mp (stableRescaledFlow_variational_equation hK hc hm hu hw hr.1 v) 1).congr_deriv
    simp [A, F, q, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    ring
  have hA (r : ℝ) (hr : r ∈ Icc 0 s) (i : Unit) : signedRowSum (A r) i ≤ -(3 * K / 16) := by
    obtain ⟨hm', hu', hw'⟩ := stableRescaledFlow_band hc hm hu hw hr.1
    simpa [A, Y, signedRowSum, K, neg_div] using stableRescaledJacobian_strong_diagonal hc hm' hu' hw'
  have hq (r : ℝ) (hr : r ∈ Icc 0 s) : ‖q r‖ ≤ 96 * |y 1| * M * Real.exp (-2 * (3 * K / 16) * r) := by
    obtain ⟨hm', hu', hw'⟩ := stableRescaledFlow_band hc hm hu hw hr.1
    have h0 := (stableRescaledJacobian_center_column hc hm' hu' hw').1
    have h2 := stableRescaledJacobian_strong_weak hc hm' hu' hw'
    have hsmall : |Y r 1| + |Y r 2| ≤ 1 := by change |Y r 1| ≤ 1 / 100 at hu'; change |Y r 2| ≤ 1 / 100 at hw'; linarith
    have h2' : |K * stableOriginalJacobian (Y r) 1 2| ≤ 18 * |Y r 1| :=
      h2.trans (mul_le_of_le_one_right (by positivity) hsmall)
    have hJ (i : Fin 3) : |J r i| ≤ M := by
      have H : |J r i| ≤ ‖J r‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm (J r) i
      exact H.trans (stableRescaledDifferential_bound hc hm hu hw hr.1 v)
    have hsum : |q r ()| ≤ 96 * |Y r 1| * M := by
      have H := abs_add_le (K * stableOriginalJacobian (Y r) 1 0 * J r 0)
        (K * stableOriginalJacobian (Y r) 1 2 * J r 2)
      have H0 := mul_le_mul h0 (hJ 0) (abs_nonneg _) (by positivity)
      have H2 := mul_le_mul h2' (hJ 2) (abs_nonneg _) (by positivity)
      change |q r ()| ≤ _ at H
      simp only [abs_mul] at H H0 H2
      nlinarith only [H, H0, H2, mul_nonneg (abs_nonneg (Y r 1)) hM]
    have hU := (stableRescaledFlow_wall_decay hc hm hu hw hr.1).1
    have H := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hU (by norm_num : (0 : ℝ) ≤ 96)) hM
    have heq : -3 * K / 8 * r = -2 * (3 * K / 16) * r := by ring
    simp only [K] at heq
    rw [heq] at H
    have htail : |q r ()| ≤ 96 * |y 1| * M * Real.exp (-2 * (3 * K / 16) * r) := by
      exact hsum.trans (by nlinarith only [H])
    simpa only [q, pi_norm_const, Real.norm_eq_abs] using htail
  have H := norm_le_exp_of_faster_forcing (ρ := 3 * K / 16) (Q := 96 * |y 1| * M)
    (by positivity) (by positivity) hF hA hq s ⟨hs, le_rfl⟩
  have hzero : F 0 = fun _ : Unit => v 1 := by
    simp only [F, J, stableRescaledDifferential_initial, ContinuousLinearMap.id_apply]
  rw [hzero] at H
  simp only [F, pi_norm_const, Real.norm_eq_abs] at H
  convert! H using 1
  dsimp [M, K]
  congr 1
  · field_simp
    ring
  · congr 1
    ring

theorem stableRescaledDifferential_strong_zero {y v : StableState} {c s : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 40)
    (hu : |y 1| ≤ 1 / 200) (hw : |y 2| ≤ 1 / 200) (hs : 0 ≤ s)
    (hy : y 1 = 0) (hv : v 1 = 0) :
    stableRescaledDifferential (c + 1) y s v 1 = 0 := by
  have H := stableRescaledDifferential_strong_decay hc hm hu hw hs v
  apply abs_eq_zero.mp
  apply le_antisymm _ (abs_nonneg _)
  simpa only [hy, hv, abs_zero, mul_zero, zero_mul, zero_div, zero_add] using H

end BianchiIX
