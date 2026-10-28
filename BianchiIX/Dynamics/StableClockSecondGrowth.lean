import BianchiIX.Dynamics.StableClockHessian
import BianchiIX.Dynamics.StableClockSecondVariation
import BianchiIX.Analysis.ForcedBudgetGrowth

noncomputable section

namespace BianchiIX

open Set

theorem stableClockFlow_second_variation_initial {c : ℝ} {y : StableState}
    (hc : 2 ≤ c) (hy : y ∈ stableParameterDomain c) (v w : StableState) :
    fderiv ℝ (fderiv ℝ (fun z => stableClockFlow c (z, 0))) y v w = 0 := by
  obtain ⟨Q, h0, hQ⟩ := exists_stableClockFlow_second_variation (T := 0) hc hy v w
  exact (hQ 0 ⟨le_rfl, le_rfl⟩).1.symm.trans h0

theorem stableClockFlow_second_variation_bound {c σ : ℝ} {y : StableState}
    (hc : 2 ≤ c) (hy : y ∈ stableParameterDomain c) (hσ : 0 ≤ σ) (v w : StableState) :
    ‖fderiv ℝ (fderiv ℝ (fun z => stableClockFlow c (z, σ))) y v w‖ ≤
      1632 * Real.exp (32 * (|y 1| + |y 2|)) ^ 3 * stableSecondInputWeight (|y 1| + |y 2|) v w := by
  obtain ⟨Q, h0, hQ⟩ := exists_stableClockFlow_second_variation (T := σ) hc hy v w
  let b := |y 1| + |y 2|
  let C := 204 * Real.exp (32 * b) ^ 2 * stableSecondInputWeight b v w
  let Y := fun s => stableClockFlow c (y, s)
  let A := fun s => stableClockJacobian c (Y s)
  let q := fun s => fderiv ℝ (fderiv ℝ (stableClockField c)) (Y s)
    (fderiv ℝ (stableClockFlow c) (y, s) (v, 0))
    (fderiv ℝ (stableClockFlow c) (y, s) (w, 0))
  let E := fun s => -32 * b * (1 - Real.exp (-s / 4))
  let B := fun s => 8 * C * (1 - Real.exp (-s / 8))
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hC : 0 ≤ C := mul_nonneg (by positivity) (stableSecondInputWeight_nonneg hb v w)
  have hf (s : ℝ) (hs : s ∈ Icc 0 σ) : HasDerivAt Q ((A s).mulVec (Q s) + q s) s := by
    simpa only [stableClockField_fderiv_matrix] using (hQ s hs).2
  have hE (s : ℝ) : HasDerivAt E (-8 * b * Real.exp (-s / 4)) s := by
    convert! ((hasDerivAt_const s (1 : ℝ)).sub (((hasDerivAt_id s).neg.div_const 4).exp)).const_mul
      (-32 * b) using 1
    dsimp
    ring
  have hA (s : ℝ) (hs : s ∈ Icc 0 σ) (i : Fin 3) :
      signedRowSum (A s) i ≤ -(-8 * b * Real.exp (-s / 4)) := by
    obtain ⟨hm, hu, hw⟩ := stableClockFlow_band hc hy hs.1
    have H := stableClockJacobian_signedRowSum hc hm
      (hu.trans (by linarith [hy.2.1])) (hw.trans (by linarith [hy.2.2])) i
    have H' := mul_le_mul_of_nonneg_left (stableClockFlow_amplitude_decay hc hy hs.1)
      (by norm_num : (0 : ℝ) ≤ 8)
    exact H.trans (by nlinarith only [H'])
  have hEa (s : ℝ) (hs : s ∈ Icc 0 σ) : E s ≤ E 0 := by
    have he := Real.exp_le_one_iff.mpr (by linarith [hs.1] : -s / 4 ≤ 0)
    have H := mul_nonneg hb (sub_nonneg.mpr he)
    dsimp [E]
    simp only [neg_zero, zero_div, Real.exp_zero, sub_self, mul_zero]
    nlinarith only [H]
  have hB (s : ℝ) : HasDerivAt B (C * Real.exp (-s / 8)) s := by
    convert! ((hasDerivAt_const s (1 : ℝ)).sub (((hasDerivAt_id s).neg.div_const 8).exp)).const_mul
      (8 * C) using 1
    dsimp
    ring
  have hsource (s : ℝ) (hs : s ∈ Icc 0 σ) : ‖q s‖ ≤ C * Real.exp (-s / 8) :=
    stableClockFlow_second_forcing_decay hc hy hs.1 v w
  have H := norm_le_exp_of_forced_budget hf (fun s _ => hE s) hA hEa (fun s _ => hB s)
    (by simp [h0, B]) hsource σ ⟨hσ, le_rfl⟩
  have hEB : E 0 - E σ ≤ 32 * b := by
    dsimp [E]
    simp only [neg_zero, zero_div, Real.exp_zero, sub_self, mul_zero]
    nlinarith [mul_nonneg hb (Real.exp_pos (-σ / 4)).le]
  have hBB : B σ ≤ 8 * C := by
    dsimp [B]
    nlinarith [mul_nonneg hC (Real.exp_pos (-σ / 8)).le]
  have hBpos : 0 ≤ B σ := by
    dsimp [B]
    exact mul_nonneg (by positivity) (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith)))
  have H' := H.trans (mul_le_mul (Real.exp_le_exp.mpr hEB) hBB hBpos (Real.exp_pos _).le)
  rw [(hQ σ ⟨hσ, le_rfl⟩).1] at H'
  convert! H' using 1
  dsimp [C, b]
  ring

end BianchiIX
