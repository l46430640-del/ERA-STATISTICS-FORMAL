import BianchiIX.Analysis.ExitTailJacobianNorm
import BianchiIX.Analysis.ExitTailCompactDerivatives
import BianchiIX.Dynamics.ExitTailPrefix

noncomputable section

namespace BianchiIX

open Set MeasureTheory

theorem continuousOn_exitTail_stateDerivative {Y : ℝ → ExitTailState} {T α b A D : ℝ}
    (hY : ContinuousOn Y (Icc 0 T)) (hreg : ∀ s ∈ Icc 0 T, exitTailRegion α b A D (Y s)) :
    ContinuousOn (fun s => fderiv ℝ (exitTailField (Real.exp (-s))) (Y s)) (Icc 0 T) := by
  have hpair : ContinuousOn (fun s => (Real.exp (-s), Y s)) (Icc 0 T) :=
    (by fun_prop : ContinuousOn (fun s : ℝ => Real.exp (-s)) (Icc 0 T)).prodMk hY
  intro s hs
  have hv : 0 ≤ Real.exp (-s) ∧ Real.exp (-s) ≤ 1 :=
    ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr (neg_nonpos.mpr hs.1)⟩
  have hR := (hreg s hs).1
  have hvR : Real.exp (-s) ^ 2 < (Y s 0) ^ 2 := by nlinarith only [hR.1, hv.1, hv.2]
  have hR0 : Y s 0 ≠ 0 := by linarith only [hR.1]
  have hd : exitTailSpeed (Y s 0) (Y s 1) (Real.exp (-s)) (Y s 2) ≠ 0 := by
    have H := exitTailSpeed_compact hR.1 (hreg s hs).2.1 hv (hreg s hs).2.2.1
    linarith only [H]
  have H := (contDiffAt_exitTail_stateDerivative 0 hvR hR0 hd).continuousAt
  exact H.comp_continuousWithinAt
    (f := fun r : ℝ => (Real.exp (-r), Y r)) (hpair s hs)

/-- The same scalar budget that bounds the wall multipliers also bounds the full Jacobian integral. -/
theorem exitTail_jacobian_integral_bound {Y : ℝ → ExitTailState} {T α b A D : ℝ}
    (hT : 0 ≤ T) (hα : 0 ≤ α) (hb : 0 ≤ b) (hA : 0 ≤ A)
    (hY : ContinuousOn Y (Icc 0 T))
    (hreg : ∀ s ∈ Icc 0 T, exitTailRegion α b A D (Y s)) :
    (∫ s in (0 : ℝ)..T, ‖fderiv ℝ (exitTailField (Real.exp (-s))) (Y s)‖) ≤
      2 * exitTailRateBudget α b A D T + 2048 * (1 + A * b * T) := by
  let a := 20 * (α + D * b) + 200 * (A * b) ^ 2 + 2048 * A * b
  let c := 200 * A * b + 2048
  have hc : 0 ≤ c := by dsimp only [c]; positivity
  have hcontinuous := (continuousOn_exitTail_stateDerivative hY hreg).norm
  have HE := integral_abs_le_exit_tail_envelope hT hc (by norm_num : (0 : ℝ) ≤ 20)
    hcontinuous (A := a) ?_
  · have H : (∫ s in (0 : ℝ)..T, ‖fderiv ℝ (exitTailField (Real.exp (-s))) (Y s)‖) ≤
        a * T + c + 20 / 2 := by simpa only [abs_norm] using HE
    apply H.trans_eq
    dsimp only [a, c, exitTailRateBudget]
    ring
  · intro s hs
    rw [abs_norm]
    have hv : 0 ≤ Real.exp (-s) ∧ Real.exp (-s) ≤ 1 :=
      ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr (neg_nonpos.mpr hs.1)⟩
    obtain ⟨hR, hu, hw, hsum, hrad⟩ := hreg s hs
    have H0 := exitTailWallRate_abs hα hR hu hv hw 0
    have H1 := exitTailWallRate_abs hα hR hu hv hw 1
    have HJ := exitTailField_jacobian_norm_bound hR hu hv hw
    have hsq := (sq_le_sq₀ (add_nonneg (abs_nonneg _) (abs_nonneg _)) (mul_nonneg hA hb)).mpr hsum
    have hm := mul_le_mul_of_nonneg_right hsum hv.1
    have he : Real.exp (-s) ^ 2 = Real.exp (-2 * s) := by
      rw [sq, ← Real.exp_add]
      congr 1
      ring
    rw [he] at H0 H1
    dsimp only [a, c]
    nlinarith only [H0, H1, HJ, hsq, hm, hrad, hsum]

end BianchiIX
