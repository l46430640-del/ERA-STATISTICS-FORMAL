import BianchiIX.Dynamics.StableSecondForcing
import BianchiIX.Analysis.ForcedBudgetGrowth

noncomputable section

namespace BianchiIX

open Set

theorem stableRescaledSecondDifferential_bound {y : StableState} {c s : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| < 1 / 40)
    (hu : |y 1| < 1 / 200) (hw : |y 2| < 1 / 200) (hs : 0 ≤ s) (v w : StableState) :
    ‖stableRescaledSecondDifferential (c + 1) y s v w‖ ≤
      40000 * Real.exp (512 * (|y 1| + |y 2|)) ^ 3 * ‖v‖ * ‖w‖ := by
  let b := |y 1| + |y 2|
  let E := Real.exp (512 * b)
  let Q := 10000 * E ^ 2 * ‖v‖ * ‖w‖
  let f := fun r => stableSecondIntegral (c + 1) y w r v
  let Y := stableRescaledFlow (c + 1) y
  let A := fun r => (c + 1) • stableOriginalJacobian (Y r)
  let q := fun r => (c + 1) • stableOriginalHessian (Y r)
    (stableRescaledDifferential (c + 1) y r v) (stableRescaledDifferential (c + 1) y r w)
  let e := fun r => 512 * b * Real.exp (-r / 2)
  let e' := fun r => -256 * b * Real.exp (-r / 2)
  let B := fun r => 4 * Q * (1 - Real.exp (-r / 4))
  let B' := fun r => Q * Real.exp (-r / 4)
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hK : 0 < c + 1 := by linarith
  have hf (r : ℝ) (hr : r ∈ Icc 0 s) : HasDerivAt f ((A r).mulVec (f r) + q r) r := by
    simpa only [A, Matrix.smul_mulVec, smul_add] using
      stableSecondIntegral_variational_equation hK hc hm hu hw hr.1 v w
  have he (r : ℝ) : HasDerivAt e (e' r) r := by
    convert! (((hasDerivAt_id r).neg.div_const 2).exp).const_mul (512 * b) using 1
    dsimp [e']
    ring
  have hrow (r : ℝ) (hr : r ∈ Icc 0 s) (i : Fin 3) : signedRowSum (A r) i ≤ -e' r := by
    obtain ⟨hm', hu', hw'⟩ := stableRescaledFlow_band hc hm.le hu.le hw.le hr.1
    have H := (stableRescaledJacobian_signedRowSum hc hm' hu' hw' i).trans
      (mul_le_mul_of_nonneg_left (stableRescaledFlow_amplitude_decay hc hm.le hu.le hw.le hr.1)
        (by norm_num : (0 : ℝ) ≤ 256))
    convert! H using 1
    dsimp [e', b]
    ring
  have he0 : e 0 = 512 * b := by simp [e]
  have hEa (r : ℝ) (hr : r ∈ Icc 0 s) : e r ≤ e 0 := by
    rw [he0]
    dsimp [e]
    have H := Real.exp_le_one_iff.mpr (show -r / 2 ≤ 0 by linarith [hr.1])
    nlinarith only [mul_le_mul_of_nonneg_left H (show 0 ≤ 512 * b by positivity)]
  have hB (r : ℝ) : HasDerivAt B (B' r) r := by
    convert! ((hasDerivAt_const r (1 : ℝ)).sub
      (((hasDerivAt_id r).neg.div_const 4).exp)).const_mul (4 * Q) using 1
    dsimp [B']
    ring
  have hinit : ‖f 0‖ ≤ B 0 := by simp [f, B, stableSecondIntegral_initial]
  have hq (r : ℝ) (hr : r ∈ Icc 0 s) : ‖q r‖ ≤ B' r :=
    stableSecondForcing_decay hc hm.le hu.le hw.le hr.1 v w
  have H := norm_le_exp_of_forced_budget hf (fun r _ => he r) hrow hEa (fun r _ => hB r)
    hinit hq s ⟨hs, le_rfl⟩
  have hBs : B s ≤ 4 * Q := by
    dsimp [B]
    nlinarith [Real.exp_pos (-s / 4)]
  have hEs : Real.exp (e 0 - e s) ≤ E := by
    apply Real.exp_le_exp.mpr
    rw [he0]
    have H : 0 ≤ e s := by dsimp [e]; positivity
    linarith
  have H' := (H.trans (mul_le_mul_of_nonneg_left hBs (Real.exp_pos _).le)).trans
    (mul_le_mul_of_nonneg_right hEs (by positivity : 0 ≤ 4 * Q))
  rw [stableRescaledSecondDifferential_eq_integral hK hc hm hu hw hs v w]
  convert! H' using 1
  dsimp [Q, E, b]
  ring

theorem stableRescaledSecondDifferential_opNorm_bound {y : StableState} {c s : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| < 1 / 40)
    (hu : |y 1| < 1 / 200) (hw : |y 2| < 1 / 200) (hs : 0 ≤ s) :
    ‖stableRescaledSecondDifferential (c + 1) y s‖ ≤
      40000 * Real.exp (512 * (|y 1| + |y 2|)) ^ 3 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro w
  exact stableRescaledSecondDifferential_bound hc hm hu hw hs v w

end BianchiIX
