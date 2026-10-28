import BianchiIX.Dynamics.StableClockSecondGrowth
import BianchiIX.Dynamics.StableClockStrongSecondForcing
import BianchiIX.Analysis.SlowForcingDecay

noncomputable section

namespace BianchiIX

open Set

theorem stableClockJacobian_strong_offDiagonal {c : ℝ} {y v : StableState}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 10) (hw : |y 2| ≤ 1 / 100) :
    |stableClockJacobian c y 1 0 * v 0 + stableClockJacobian c y 1 2 * v 2| ≤
      2 * |y 1| * ‖v‖ := by
  have H0 := mul_le_mul (stableClockJacobian_center_column hc hm).1
    (show |v 0| ≤ ‖v‖ by simpa only [Real.norm_eq_abs] using norm_le_pi_norm v 0)
    (abs_nonneg _) (abs_nonneg _)
  have H2 := mul_le_mul (stableClockJacobian_strong_weak hc hw)
    (show |v 2| ≤ ‖v‖ by simpa only [Real.norm_eq_abs] using norm_le_pi_norm v 2)
    (abs_nonneg _) (abs_nonneg _)
  have H := abs_add_le (stableClockJacobian c y 1 0 * v 0) (stableClockJacobian c y 1 2 * v 2)
  simp only [abs_mul] at H
  nlinarith only [H, H0, H2]

theorem stableClockFlow_strong_second_variation_decay {c σ : ℝ} {y : StableState}
    (hc : 2 ≤ c) (hy : y ∈ stableParameterDomain c) (hσ : 0 ≤ σ) (v w : StableState) :
    |fderiv ℝ (fderiv ℝ (fun z => stableClockFlow c (z, σ))) y v w 1| ≤
      560000 * Real.exp (32 * (|y 1| + |y 2|)) ^ 3 * stableStrongHessianBudget y v w /
        (c + 1) * Real.exp (-(c + 1) / 16 * σ) := by
  obtain ⟨Q, h0, hQ⟩ := exists_stableClockFlow_second_variation (T := σ) hc hy v w
  let K := c + 1
  let E := Real.exp (32 * (|y 1| + |y 2|))
  let B := stableStrongHessianBudget y v w
  let W := stableSecondInputWeight (|y 1| + |y 2|) v w
  let Y := fun s => stableClockFlow c (y, s)
  let H := fun s => fderiv ℝ (fderiv ℝ (stableClockField c)) (Y s)
    (fderiv ℝ (stableClockFlow c) (y, s) (v, 0))
    (fderiv ℝ (stableClockFlow c) (y, s) (w, 0))
  let F : ℝ → (Unit → ℝ) := fun s _ => Q s 1
  let A : ℝ → Matrix Unit Unit ℝ := fun s _ _ => stableClockJacobian c (Y s) 1 1
  let q : ℝ → (Unit → ℝ) := fun s _ =>
    stableClockJacobian c (Y s) 1 0 * Q s 0 + stableClockJacobian c (Y s) 1 2 * Q s 2 + H s 1
  have hK : 0 < K := by dsimp [K]; linarith
  have hE : 1 ≤ E := Real.one_le_exp (by positivity)
  have hB : 0 ≤ B := stableStrongHessianBudget_nonneg y v w
  have hW : 0 ≤ W := stableSecondInputWeight_nonneg (by positivity) v w
  have hQbound (s : ℝ) (hs : s ∈ Icc 0 σ) : ‖Q s‖ ≤ 1632 * E ^ 3 * W := by
    rw [(hQ s hs).1]
    exact stableClockFlow_second_variation_bound hc hy hs.1 v w
  have hF (s : ℝ) (hs : s ∈ Icc 0 σ) : HasDerivAt F ((A s).mulVec (F s) + q s) s := by
    apply hasDerivAt_pi.mpr
    intro i
    have HD := (hQ s hs).2
    rw [stableClockField_fderiv_matrix] at HD
    apply (hasDerivAt_pi.mp HD 1).congr_deriv
    simp [A, F, q, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    ring
  have hA (s : ℝ) (hs : s ∈ Icc 0 σ) (i : Unit) : signedRowSum (A s) i ≤ -2 * (K / 16) := by
    obtain ⟨hm, hu, hw⟩ := stableClockFlow_band hc hy hs.1
    have Hrow := (stableClockJacobian_stable_rows hc hm
      (hu.trans (by linarith [hy.2.1])) (hw.trans (by linarith [hy.2.2]))).1
    simp only [A, signedRowSum, Finset.univ_unique, Finset.erase_singleton,
      Finset.sum_empty, add_zero]
    dsimp only [Y, K]
    linarith [abs_nonneg (stableClockJacobian c (stableClockFlow c (y, s)) 1 2)]
  have hq (s : ℝ) (hs : s ∈ Icc 0 σ) :
      ‖q s‖ ≤ (35000 * E ^ 3 * B) * Real.exp (-(K / 16) * s) := by
    let e := Real.exp (-(K / 16) * s)
    have he : 0 ≤ e := (Real.exp_pos _).le
    obtain ⟨hm, _, hw⟩ := stableClockFlow_band hc hy hs.1
    have hU : |Y s 1| ≤ |y 1| * e := (stableClockFlow_wall_decay hc hy hs.1).1.trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by dsimp [K]; nlinarith [hs.1]))
        (abs_nonneg (y 1)))
    have Hoff := stableClockJacobian_strong_offDiagonal (v := Q s) hc hm
      (hw.trans (by linarith [hy.2.2]))
    have HP := mul_le_mul (mul_le_mul_of_nonneg_left hU (by norm_num : (0 : ℝ) ≤ 2))
      (hQbound s hs) (norm_nonneg _) (by positivity)
    have HI := mul_le_mul_of_nonneg_left
      (stableStrongHessianBudget_controls_input (by linarith [hy.2.1, hy.2.2]) v w)
      (show 0 ≤ 3264 * E ^ 3 * e by positivity)
    have HF := stableClockFlow_strong_second_forcing_decay hc hy hs.1 v w
    have hE23 : E ^ 2 ≤ E ^ 3 := by
      nlinarith only [mul_le_mul_of_nonneg_left hE (sq_nonneg E)]
    have HE := mul_le_mul_of_nonneg_right hE23 (show 0 ≤ 25000 * B * e by positivity)
    have HT := abs_add_le
      (stableClockJacobian c (Y s) 1 0 * Q s 0 + stableClockJacobian c (Y s) 1 2 * Q s 2)
      (H s 1)
    have heq : -(c + 1) / 16 * s = -(K / 16) * s := by dsimp [K]; ring
    rw [heq] at HF
    change |H s 1| ≤ 25000 * E ^ 2 * B * e at HF
    change (3264 * E ^ 3 * e) * (|y 1| * W) ≤ (3264 * E ^ 3 * e) * (3 * B) at HI
    have htail : |q s ()| ≤ 35000 * E ^ 3 * B * e := by
      dsimp only [q]
      nlinarith only [HT, Hoff, HP, HI, HF, HE, show 0 ≤ E ^ 3 * B * e by positivity]
    simpa only [q, pi_norm_const, Real.norm_eq_abs] using htail
  have HB := norm_le_exp_of_slower_forcing (ρ := K / 16) (Q := 35000 * E ^ 3 * B)
    (by positivity) (by positivity) hF hA hq σ ⟨hσ, le_rfl⟩
  have hzero : F 0 = 0 := by ext i; simp [F, h0]
  rw [hzero, norm_zero, zero_add] at HB
  simp only [F, pi_norm_const, Real.norm_eq_abs] at HB
  rw [(hQ σ ⟨hσ, le_rfl⟩).1] at HB
  convert! HB using 1
  dsimp [E, B, K]
  congr 1
  · field_simp
    ring
  · congr 1
    ring

theorem stableClockFlow_strong_second_variation_zero {c σ : ℝ} {y v w : StableState}
    (hc : 2 ≤ c) (hy : y ∈ stableParameterDomain c) (hσ : 0 ≤ σ)
    (hy1 : y 1 = 0) (hv1 : v 1 = 0) (hw1 : w 1 = 0) :
    fderiv ℝ (fderiv ℝ (fun z => stableClockFlow c (z, σ))) y v w 1 = 0 := by
  apply abs_eq_zero.mp
  apply le_antisymm _ (abs_nonneg _)
  simpa only [stableStrongHessianBudget, hy1, hv1, hw1, abs_zero, mul_zero, zero_mul,
    zero_div, zero_add, add_zero] using stableClockFlow_strong_second_variation_decay hc hy hσ v w

end BianchiIX
