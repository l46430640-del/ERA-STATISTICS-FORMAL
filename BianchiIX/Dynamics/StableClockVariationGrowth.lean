import BianchiIX.Dynamics.StableClockVariation
import BianchiIX.Dynamics.StableClockJacobian

noncomputable section

namespace BianchiIX

open Set

theorem stableClockFlow_amplitude_decay {c σ : ℝ} {y : StableState}
    (hc : 2 ≤ c) (hy : y ∈ stableParameterDomain c) (hσ : 0 ≤ σ) :
    |stableClockFlow c (y, σ) 1| + |stableClockFlow c (y, σ) 2| ≤
      (|y 1| + |y 2|) * Real.exp (-σ / 4) := by
  obtain ⟨hu, hw⟩ := stableClockFlow_wall_decay hc hy hσ
  have he : Real.exp (-(c + 1) / 8 * σ) ≤ Real.exp (-σ / 4) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hU := hu.trans (mul_le_mul_of_nonneg_left he (abs_nonneg (y 1)))
  have hexp : -(1 / 4 : ℝ) * σ = -σ / 4 := by ring
  rw [hexp] at hw
  nlinarith only [hU, hw]

theorem stableClockFlow_variational_equation {c σ : ℝ} {y : StableState}
    (hc : 2 ≤ c) (hy : y ∈ stableParameterDomain c) (hσ : 0 ≤ σ) (v : StableState) :
    HasDerivAt (fun s => fderiv ℝ (stableClockFlow c) (y, s) (v, 0))
      ((stableClockJacobian c (stableClockFlow c (y, σ))).mulVec
        (fderiv ℝ (stableClockFlow c) (y, σ) (v, 0))) σ := by
  simpa only [stableClockVariationRate, stableClockField_fderiv_matrix] using
    hasDerivAt_stableClockFlow_variation hc hy hσ v

theorem stableClockFlow_variation_bound {c σ : ℝ} {y : StableState}
    (hc : 2 ≤ c) (hy : y ∈ stableParameterDomain c) (hσ : 0 ≤ σ) (v : StableState) :
    ‖fderiv ℝ (stableClockFlow c) (y, σ) (v, 0)‖ ≤
      Real.exp (32 * (|y 1| + |y 2|)) * ‖v‖ := by
  let b := |y 1| + |y 2|
  let J := fun s => fderiv ℝ (stableClockFlow c) (y, s) (v, 0)
  let A := fun s => stableClockJacobian c (stableClockFlow c (y, s))
  let z := fun s => 32 * b * (1 - Real.exp (-s / 4))
  have hJ (s : ℝ) (hs : s ∈ Icc 0 σ) : HasDerivAt J ((A s).mulVec (J s)) s :=
    stableClockFlow_variational_equation hc hy hs.1 v
  have hz (s : ℝ) : HasDerivAt z (8 * b * Real.exp (-s / 4)) s := by
    convert! ((hasDerivAt_const s (1 : ℝ)).sub (((hasDerivAt_id s).neg.div_const 4).exp)).const_mul
      (32 * b) using 1
    dsimp
    ring
  have hrow (s : ℝ) (hs : s ∈ Ico 0 σ) (i : Fin 3) :
      signedRowSum (A s) i ≤ 8 * b * Real.exp (-s / 4) := by
    obtain ⟨hm, hu, hw⟩ := stableClockFlow_band hc hy hs.1
    have H := stableClockJacobian_signedRowSum hc hm
      (hu.trans (by linarith [hy.2.1])) (hw.trans (by linarith [hy.2.2])) i
    have H' := mul_le_mul_of_nonneg_left (stableClockFlow_amplitude_decay hc hy hs.1)
      (by norm_num : (0 : ℝ) ≤ 8)
    exact H.trans (by nlinarith only [H'])
  have H := norm_le_exp_of_signedRowSum (HasDerivAt.continuousOn hJ)
    (fun s hs => hJ s (Ico_subset_Icc_self hs))
    (HasDerivAt.continuousOn (fun s _ => hz s)) (fun s _ => hz s) hrow σ ⟨hσ, le_rfl⟩
  have hzero : J 0 = v := stableClockFlow_variation_initial hc hy v
  have hz0 : z 0 = 0 := by simp [z]
  rw [hzero, hz0, sub_zero] at H
  have hzb : z σ ≤ 32 * b := by
    have hb : 0 ≤ b := by dsimp [b]; positivity
    dsimp [z]
    nlinarith [Real.exp_pos (-σ / 4)]
  have H' := H.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hzb) (norm_nonneg v))
  simpa only [mul_comm] using H'

theorem stableClockFlow_initialDerivative_opNorm {c σ : ℝ} {y : StableState}
    (hc : 2 ≤ c) (hy : y ∈ stableParameterDomain c) (hσ : 0 ≤ σ) :
    ‖fderiv ℝ (fun z => stableClockFlow c (z, σ)) y‖ ≤ Real.exp (32 * (|y 1| + |y 2|)) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.exp_pos _).le
  intro v
  rw [fderiv_parameterSlice_apply ((contDiffAt_stableClockFlow_two hc hy hσ).differentiableAt (by norm_num))]
  exact stableClockFlow_variation_bound hc hy hσ v

end BianchiIX
