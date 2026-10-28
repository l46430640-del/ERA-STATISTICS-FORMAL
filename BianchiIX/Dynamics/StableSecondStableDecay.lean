import BianchiIX.Dynamics.StableSecondGrowth

noncomputable section

namespace BianchiIX

open Set

theorem stableSecondIntegral_stable_equation {K : ℝ} {y : StableState} {c s : ℝ}
    (hK : 0 < K) (hc : 2 ≤ c) (hm : |y 0 - c| < 1 / 40)
    (hu : |y 1| < 1 / 200) (hw : |y 2| < 1 / 200) (hs : 0 ≤ s) (v w : StableState) :
    HasDerivAt (fun r => ![stableSecondIntegral K y w r v 1, stableSecondIntegral K y w r v 2])
      ((stableLinearBlock K (stableRescaledFlow K y s)).mulVec
          ![stableSecondIntegral K y w s v 1, stableSecondIntegral K y w s v 2] +
        stableSecondIntegral K y w s v 0 • stableCenterColumn K (stableRescaledFlow K y s) +
        ![(K • stableOriginalHessian (stableRescaledFlow K y s)
            (stableRescaledDifferential K y s v) (stableRescaledDifferential K y s w)) 1,
          (K • stableOriginalHessian (stableRescaledFlow K y s)
            (stableRescaledDifferential K y s v) (stableRescaledDifferential K y s w)) 2]) s := by
  have H := hasDerivAt_pi.mp (stableSecondIntegral_variational_equation hK hc hm hu hw hs v w)
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · apply (H 1).congr_deriv
    simp [stableLinearBlock, stableCenterColumn, Matrix.vecHead, Matrix.vecTail,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    ring
  · apply (H 2).congr_deriv
    simp [stableLinearBlock, stableCenterColumn, Matrix.vecHead, Matrix.vecTail,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    ring

theorem stableRescaledSecondDifferential_stable_decay {y : StableState} {c s : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| < 1 / 40)
    (hu : |y 1| < 1 / 200) (hw : |y 2| < 1 / 200) (hs : 0 ≤ s) (v w : StableState) :
    ‖![stableRescaledSecondDifferential (c + 1) y s v w 1,
       stableRescaledSecondDifferential (c + 1) y s v w 2]‖ ≤
      (512 * (|y 1| + |y 2|) * (40000 * Real.exp (512 * (|y 1| + |y 2|)) ^ 3) +
        80000 * Real.exp (512 * (|y 1| + |y 2|)) ^ 2) * ‖v‖ * ‖w‖ * Real.exp (-s / 8) := by
  let b := |y 1| + |y 2|
  let E := Real.exp (512 * b)
  let M := 40000 * E ^ 3 * ‖v‖ * ‖w‖
  let Q := 10000 * E ^ 2 * ‖v‖ * ‖w‖
  let I := fun r => stableSecondIntegral (c + 1) y w r v
  let Z := fun r => ![I r 1, I r 2]
  let Y := stableRescaledFlow (c + 1) y
  let A := fun r => stableLinearBlock (c + 1) (Y r)
  let q0 := fun r => I r 0 • stableCenterColumn (c + 1) (Y r)
  let q1 := fun r => (c + 1) • stableOriginalHessian (Y r)
    (stableRescaledDifferential (c + 1) y r v) (stableRescaledDifferential (c + 1) y r w)
  let q := fun r => q0 r + ![q1 r 1, q1 r 2]
  have hK : 0 < c + 1 := by linarith
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hI (r : ℝ) (hr : 0 ≤ r) : I r = stableRescaledSecondDifferential (c + 1) y r v w :=
    (stableRescaledSecondDifferential_eq_integral hK hc hm hu hw hr v w).symm
  have hZ (r : ℝ) (hr : r ∈ Icc 0 s) : HasDerivAt Z ((A r).mulVec (Z r) + q r) r := by
    simpa only [q, add_assoc] using stableSecondIntegral_stable_equation hK hc hm hu hw hr.1 v w
  have hA (r : ℝ) (hr : r ∈ Icc 0 s) (i : Fin 2) : signedRowSum (A r) i ≤ -(1 / 8) := by
    obtain ⟨hm', hu', hw'⟩ := stableRescaledFlow_band hc hm.le hu.le hw.le hr.1
    exact (stableLinearBlock_signedRowSum hc hm' hu' hw' i).trans (by norm_num)
  have hq (r : ℝ) (hr : r ∈ Icc 0 s) : ‖q r‖ ≤ (64 * b * M + Q) * Real.exp (-r / 4) := by
    obtain ⟨hm', hu', hw'⟩ := stableRescaledFlow_band hc hm.le hu.le hw.le hr.1
    have hI0 : |I r 0| ≤ M := by
      have H := show |I r 0| ≤ ‖I r‖ by simpa only [Real.norm_eq_abs] using norm_le_pi_norm (I r) 0
      rw [hI r hr.1] at H
      rw [hI r hr.1]
      exact H.trans (stableRescaledSecondDifferential_bound hc hm hu hw hr.1 v w)
    have hcol : ‖stableCenterColumn (c + 1) (Y r)‖ ≤ 64 * b * Real.exp (-r / 4) := by
      have H := (stableCenterColumn_norm_bound hc hm' hu' hw').trans
        (mul_le_mul_of_nonneg_left (stableRescaledFlow_amplitude_decay hc hm.le hu.le hw.le hr.1)
          (by norm_num : (0 : ℝ) ≤ 64))
      have H' := mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (by linarith [hr.1] : -r / 2 ≤ -r / 4))
        (show 0 ≤ 64 * b by positivity)
      exact H.trans (by nlinarith only [H'])
    have h0 : ‖q0 r‖ ≤ 64 * b * M * Real.exp (-r / 4) := by
      dsimp only [q0]
      rw [norm_smul, Real.norm_eq_abs]
      have H := mul_le_mul hI0 hcol (norm_nonneg _) hM
      nlinarith only [H]
    have h1 : ‖![q1 r 1, q1 r 2]‖ ≤ Q * Real.exp (-r / 4) :=
      (stableTangent_split_bounds (q1 r)).2.2.trans
        (stableSecondForcing_decay hc hm.le hu.le hw.le hr.1 v w)
    exact (norm_add_le (q0 r) ![q1 r 1, q1 r 2]).trans (by nlinarith only [h0, h1])
  have H := norm_le_exp_of_faster_forcing (ρ := (1 / 8 : ℝ)) (Q := 64 * b * M + Q)
    (by norm_num) (by positivity) hZ hA (fun r hr => by
      convert! hq r hr using 1
      congr 2
      ring) s ⟨hs, le_rfl⟩
  have hzero : Z 0 = 0 := by simp [Z, I, stableSecondIntegral_initial]
  rw [hzero, norm_zero, zero_add] at H
  have heq : Z s = ![stableRescaledSecondDifferential (c + 1) y s v w 1,
      stableRescaledSecondDifferential (c + 1) y s v w 2] := by dsimp [Z]; rw [hI s hs]
  rw [heq] at H
  convert! H using 1
  dsimp [M, Q, E, b]
  congr 1
  · ring
  · congr 1
    ring

end BianchiIX
