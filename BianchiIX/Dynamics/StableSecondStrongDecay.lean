import BianchiIX.Dynamics.StableSecondStrongForcing

noncomputable section

namespace BianchiIX

open Set

theorem stableRescaledSecondDifferential_strong_decay {y : StableState} {c s : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| < 1 / 40)
    (hu : |y 1| < 1 / 200) (hw : |y 2| < 1 / 200) (hs : 0 ≤ s) (v w : StableState) :
    |stableRescaledSecondDifferential (c + 1) y s v w 1| ≤
      (160000000 * Real.exp (512 * (|y 1| + |y 2|)) ^ 3 * stableStrongHessianBudget y v w / (c + 1)) *
        Real.exp (-3 * (c + 1) / 32 * s) := by
  let K := c + 1
  let E := Real.exp (512 * (|y 1| + |y 2|))
  let B := stableStrongHessianBudget y v w
  let Q := 15000000 * E ^ 3 * B
  let I := fun r => stableSecondIntegral K y w r v
  let Y := stableRescaledFlow K y
  let F : ℝ → (Unit → ℝ) := fun r _ => I r 1
  let A : ℝ → Matrix Unit Unit ℝ := fun r _ _ => K * stableOriginalJacobian (Y r) 1 1
  let q : ℝ → (Unit → ℝ) := fun r _ =>
    K * stableOriginalJacobian (Y r) 1 0 * I r 0 + K * stableOriginalJacobian (Y r) 1 2 * I r 2 +
      (K • stableOriginalHessian (Y r)
        (stableRescaledDifferential K y r v) (stableRescaledDifferential K y r w)) 1
  have hK : 0 < K := by dsimp [K]; linarith
  have hB : 0 ≤ B := stableStrongHessianBudget_nonneg y v w
  have hF (r : ℝ) (hr : r ∈ Icc 0 s) : HasDerivAt F ((A r).mulVec (F r) + q r) r := by
    apply hasDerivAt_pi.mpr
    intro i
    apply (hasDerivAt_pi.mp (stableSecondIntegral_variational_equation hK hc hm hu hw hr.1 v w) 1).congr_deriv
    simp [A, F, q, I, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    ring
  have hA (r : ℝ) (hr : r ∈ Icc 0 s) (i : Unit) : signedRowSum (A r) i ≤ -(3 * K / 32) := by
    obtain ⟨hm', hu', hw'⟩ := stableRescaledFlow_band hc hm.le hu.le hw.le hr.1
    have H := (stableRescaledJacobian_strong_diagonal hc hm' hu' hw').trans
      (show -3 * (c + 1) / 16 ≤ -(3 * (c + 1) / 32) by linarith)
    simpa [A, Y, signedRowSum, K] using H
  have hq (r : ℝ) (hr : r ∈ Icc 0 s) : ‖q r‖ ≤ Q * Real.exp (-2 * (3 * K / 32) * r) := by
    have H := stableSecondStrongSource_offDiagonal hc hm hu hw hr.1 v w
    rw [stableRescaledSecondDifferential_eq_integral hK hc hm hu hw hr.1 v w] at H
    have htail : |q r ()| ≤ Q * Real.exp (-2 * (3 * K / 32) * r) := by
      convert! H using 1
      dsimp [Q, E, B, K]
      congr 2
      ring
    simpa only [q, pi_norm_const, Real.norm_eq_abs] using htail
  have H := norm_le_exp_of_faster_forcing (ρ := 3 * K / 32) (Q := Q)
    (by positivity) (by dsimp [Q]; positivity) hF hA hq s ⟨hs, le_rfl⟩
  have hzero : F 0 = 0 := by ext i; simp [F, I, stableSecondIntegral_initial]
  rw [hzero, norm_zero, zero_add] at H
  simp only [F, pi_norm_const, Real.norm_eq_abs] at H
  rw [stableRescaledSecondDifferential_eq_integral hK hc hm hu hw hs v w]
  convert! H using 1
  dsimp [Q, E, B, K]
  congr 1
  · field_simp
    ring
  · congr 1
    ring

theorem stableRescaledSecondDifferential_strong_integral {y : StableState} {c t : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| < 1 / 40)
    (hu : |y 1| < 1 / 200) (hw : |y 2| < 1 / 200) (ht : 0 ≤ t) (v w : StableState) :
    (∫ s in 0..t, |stableRescaledSecondDifferential (c + 1) y s v w 1|) ≤
      ((5120000000 / 3) * Real.exp (512 * (|y 1| + |y 2|)) ^ 3 * stableStrongHessianBudget y v w) /
        (c + 1) ^ 2 := by
  have hK : 0 < c + 1 := by linarith
  have hB := stableStrongHessianBudget_nonneg y v w
  have hcont : ContinuousOn (fun s : ℝ => |stableRescaledSecondDifferential (c + 1) y s v w 1|) (Icc 0 t) := by
    intro s hs
    have H := (continuousAt_stableRescaledSecondDifferential hK hc hm.le hu.le hw.le hs.1).comp
      (f := fun r : ℝ => (y, r)) (continuousAt_const.prodMk continuousAt_id)
    have H' : ContinuousAt (fun r : ℝ => stableRescaledSecondDifferential (c + 1) y r v w) s :=
      (H.clm_apply continuousAt_const).clm_apply continuousAt_const
    exact ((continuous_apply 1).continuousAt.comp H').abs.continuousWithinAt
  have H := integral_le_of_exp_decay (c := 3 * (c + 1) / 32) ht (by positivity)
    (show 0 ≤ 160000000 * Real.exp (512 * (|y 1| + |y 2|)) ^ 3 * stableStrongHessianBudget y v w / (c + 1) by positivity)
    hcont (fun s hs => by
      convert! stableRescaledSecondDifferential_strong_decay hc hm hu hw hs.1 v w using 1
      congr 2
      ring)
  convert! H using 1
  field_simp
  ring

end BianchiIX
