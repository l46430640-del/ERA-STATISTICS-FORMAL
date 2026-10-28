import BianchiIX.Dynamics.StableClockStableVariation

noncomputable section

namespace BianchiIX

open Set

theorem stableClockJacobian_strong_weak {c : ℝ} {y : StableState}
    (hc : 2 ≤ c) (hw : |y 2| ≤ 1 / 100) :
    |stableClockJacobian c y 1 2| ≤ |y 1| := by
  have hK : 0 < c + 1 := by linarith
  change |(-y 1 * y 2) / (c + 1)| ≤ _
  rw [abs_div, abs_of_pos hK, abs_mul, abs_neg]
  apply (div_le_iff₀ hK).mpr
  exact mul_le_mul_of_nonneg_left (by linarith : |y 2| ≤ c + 1) (abs_nonneg _)

theorem stableClockFlow_strong_variation_decay {c σ : ℝ} {y : StableState}
    (hc : 2 ≤ c) (hy : y ∈ stableParameterDomain c) (hσ : 0 ≤ σ) (v : StableState) :
    |fderiv ℝ (stableClockFlow c) (y, σ) (v, 0) 1| ≤
      (|v 1| + 32 * |y 1| * Real.exp (32 * (|y 1| + |y 2|)) * ‖v‖ / (c + 1)) *
        Real.exp (-(c + 1) / 16 * σ) := by
  let K := c + 1
  let M := Real.exp (32 * (|y 1| + |y 2|)) * ‖v‖
  let Y := fun s => stableClockFlow c (y, s)
  let J := fun s => fderiv ℝ (stableClockFlow c) (y, s) (v, 0)
  let F : ℝ → (Unit → ℝ) := fun s _ => J s 1
  let A : ℝ → Matrix Unit Unit ℝ := fun s _ _ => stableClockJacobian c (Y s) 1 1
  let q : ℝ → (Unit → ℝ) := fun s _ => stableClockJacobian c (Y s) 1 0 * J s 0 +
    stableClockJacobian c (Y s) 1 2 * J s 2
  have hK : 0 < K := by dsimp [K]; linarith
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hF (s : ℝ) (hs : s ∈ Icc 0 σ) : HasDerivAt F ((A s).mulVec (F s) + q s) s := by
    apply hasDerivAt_pi.mpr
    intro i
    apply (hasDerivAt_pi.mp (stableClockFlow_variational_equation hc hy hs.1 v) 1).congr_deriv
    simp [A, F, q, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    ring
  have hA (s : ℝ) (hs : s ∈ Icc 0 σ) (i : Unit) : signedRowSum (A s) i ≤ -(K / 16) := by
    obtain ⟨hm, hu, hw⟩ := stableClockFlow_band hc hy hs.1
    have H := (stableClockJacobian_stable_rows hc hm
      (hu.trans (by linarith [hy.2.1])) (hw.trans (by linarith [hy.2.2]))).1
    simp only [A, signedRowSum, Finset.univ_unique, Finset.erase_singleton,
      Finset.sum_empty, add_zero]
    dsimp only [Y, K]
    linarith [abs_nonneg (stableClockJacobian c (stableClockFlow c (y, s)) 1 2)]
  have hq (s : ℝ) (hs : s ∈ Icc 0 σ) :
      ‖q s‖ ≤ 2 * |y 1| * M * Real.exp (-2 * (K / 16) * s) := by
    obtain ⟨hm, _, hw⟩ := stableClockFlow_band hc hy hs.1
    have h0 := (stableClockJacobian_center_column hc hm).1
    have h2 := stableClockJacobian_strong_weak hc (hw.trans (by linarith [hy.2.2]))
    have hJ (i : Fin 3) : |J s i| ≤ M :=
      (show |J s i| ≤ ‖J s‖ by simpa only [Real.norm_eq_abs] using norm_le_pi_norm (J s) i).trans
        (stableClockFlow_variation_bound hc hy hs.1 v)
    have hsum : |q s ()| ≤ 2 * |Y s 1| * M := by
      have H := abs_add_le (stableClockJacobian c (Y s) 1 0 * J s 0)
        (stableClockJacobian c (Y s) 1 2 * J s 2)
      have H0 := mul_le_mul h0 (hJ 0) (abs_nonneg _) (abs_nonneg _)
      have H2 := mul_le_mul h2 (hJ 2) (abs_nonneg _) (abs_nonneg _)
      change |q s ()| ≤ _ at H
      simp only [abs_mul] at H
      nlinarith only [H, H0, H2]
    have hU := (stableClockFlow_wall_decay hc hy hs.1).1
    have H := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hU
      (by norm_num : (0 : ℝ) ≤ 2)) hM
    have he : -(c + 1) / 8 * s = -2 * (K / 16) * s := by dsimp [K]; ring
    rw [he] at H
    have htail : |q s ()| ≤ 2 * |y 1| * M * Real.exp (-2 * (K / 16) * s) :=
      hsum.trans (by nlinarith only [H])
    simpa only [q, pi_norm_const, Real.norm_eq_abs] using htail
  have H := norm_le_exp_of_faster_forcing (ρ := K / 16) (Q := 2 * |y 1| * M)
    (by positivity) (by positivity) hF hA hq σ ⟨hσ, le_rfl⟩
  have hzero : F 0 = fun _ : Unit => v 1 := by
    simp only [F, J, stableClockFlow_variation_initial hc hy]
  rw [hzero] at H
  simp only [F, pi_norm_const, Real.norm_eq_abs] at H
  convert! H using 1
  dsimp [M, K]
  congr 1
  · field_simp
    ring
  · congr 1
    ring

theorem stableClockFlow_strong_variation_zero {c σ : ℝ} {y v : StableState}
    (hc : 2 ≤ c) (hy : y ∈ stableParameterDomain c) (hσ : 0 ≤ σ)
    (hy1 : y 1 = 0) (hv1 : v 1 = 0) :
    fderiv ℝ (stableClockFlow c) (y, σ) (v, 0) 1 = 0 := by
  apply abs_eq_zero.mp
  apply le_antisymm _ (abs_nonneg _)
  simpa only [hy1, hv1, abs_zero, mul_zero, zero_mul, zero_div, zero_add] using
    stableClockFlow_strong_variation_decay hc hy hσ v

end BianchiIX
