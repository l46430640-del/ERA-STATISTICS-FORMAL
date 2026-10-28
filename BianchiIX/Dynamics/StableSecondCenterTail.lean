import BianchiIX.Dynamics.StableSecondGrowth

noncomputable section

namespace BianchiIX

open Set

def stableSecondCenterBudget (y : StableState) : ℝ :=
  192 * (|y 1| + |y 2|) * (40000 * Real.exp (512 * (|y 1| + |y 2|)) ^ 3) +
    10000 * Real.exp (512 * (|y 1| + |y 2|)) ^ 2

theorem stableSecondCenterBudget_nonneg (y : StableState) : 0 ≤ stableSecondCenterBudget y := by
  unfold stableSecondCenterBudget
  positivity

theorem stableRescaledSecondDifferential_center_rate {y : StableState} {c s : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| < 1 / 40)
    (hu : |y 1| < 1 / 200) (hw : |y 2| < 1 / 200) (hs : 0 ≤ s) (v w : StableState) :
    |stableRescaledSecondSource (c + 1) v w (y, s) 0| ≤
      stableSecondCenterBudget y * ‖v‖ * ‖w‖ * Real.exp (-s / 4) := by
  let b := |y 1| + |y 2|
  let E := Real.exp (512 * b)
  let M := 40000 * E ^ 3 * ‖v‖ * ‖w‖
  let Q := 10000 * E ^ 2 * ‖v‖ * ‖w‖
  let Y := stableRescaledFlow (c + 1) y s
  let H := stableRescaledSecondDifferential (c + 1) y s v w
  let B := |Y 1| + |Y 2|
  let q := (c + 1) • stableOriginalHessian Y
    (stableRescaledDifferential (c + 1) y s v) (stableRescaledDifferential (c + 1) y s w)
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  obtain ⟨hm', hu', hw'⟩ := stableRescaledFlow_band hc hm.le hu.le hw.le hs
  have hB1 : B ≤ 1 := by dsimp [B, Y]; linarith
  have hH : ‖H‖ ≤ M := stableRescaledSecondDifferential_bound hc hm hu hw hs v w
  have hH0 : |H 0| ≤ M :=
    (show |H 0| ≤ ‖H‖ by simpa only [Real.norm_eq_abs] using norm_le_pi_norm H 0).trans hH
  have hHz : ‖![H 1, H 2]‖ ≤ M := (stableTangent_split_bounds H).2.2.trans hH
  have hBdec : B ≤ b * Real.exp (-s / 4) :=
    (stableRescaledFlow_amplitude_decay hc hm.le hu.le hw.le hs).trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith : -s / 2 ≤ -s / 4)) hb)
  have hlinear : |(c + 1) * (stableOriginalJacobian Y).mulVec H 0| ≤
      192 * b * M * Real.exp (-s / 4) := by
    have H0 := stableRescaledJacobian_center_apply (v := H) hc hm' hu' hw'
    have H1 := mul_le_mul_of_nonneg_left hH0 (show 0 ≤ 64 * B ^ 2 by positivity)
    have H2 := mul_le_mul_of_nonneg_left hHz (show 0 ≤ 128 * B by positivity)
    have H3 := mul_le_mul_of_nonneg_right (show B ^ 2 ≤ B by nlinarith) hM
    have H4 := mul_le_mul_of_nonneg_right hBdec hM
    nlinarith only [H0, H1, H2, H3, H4]
  have hq : |q 0| ≤ Q * Real.exp (-s / 4) :=
    (show |q 0| ≤ ‖q‖ by simpa only [Real.norm_eq_abs] using norm_le_pi_norm q 0).trans
      (stableSecondForcing_decay hc hm.le hu.le hw.le hs v w)
  have heq : stableRescaledSecondSource (c + 1) v w (y, s) 0 =
      q 0 + (c + 1) * (stableOriginalJacobian Y).mulVec H 0 := by
    dsimp [stableRescaledSecondSource, q, Y, H]
    ring
  rw [heq]
  have Hsum := (abs_add_le _ _).trans (add_le_add hq hlinear)
  convert! Hsum using 1
  dsimp [stableSecondCenterBudget, Q, M, E, b]
  ring

theorem stableRescaledSecondDifferential_center_tail {y : StableState} {c a t : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| < 1 / 40)
    (hu : |y 1| < 1 / 200) (hw : |y 2| < 1 / 200) (ha : 0 ≤ a) (hat : a ≤ t)
    (v w : StableState) :
    |stableRescaledSecondDifferential (c + 1) y t v w 0 -
      stableRescaledSecondDifferential (c + 1) y a v w 0| ≤
        4 * stableSecondCenterBudget y * ‖v‖ * ‖w‖ * Real.exp (-a / 4) := by
  let C := stableSecondCenterBudget y * ‖v‖ * ‖w‖
  have hC : 0 ≤ C :=
    mul_nonneg (mul_nonneg (stableSecondCenterBudget_nonneg y) (norm_nonneg v)) (norm_nonneg w)
  have hK : 0 < c + 1 := by linarith
  have hf (r : ℝ) (hr : r ∈ Icc a t) := hasDerivAt_pi.mp
    (hasDerivAt_stableSecondIntegral_apply hK hc hm.le hu.le hw.le (ha.trans hr.1) v w) 0
  have hcont : Continuous (fun r : ℝ => C * Real.exp (-r / 4)) := by fun_prop
  have H := abs_sub_le_integral_bound hat hf hcont.continuousOn
    (fun r hr => stableRescaledSecondDifferential_center_rate hc hm hu hw (ha.trans hr.1) v w)
  have HI := integral_le_of_exp_decay (f := fun r : ℝ => C * Real.exp (-r / 4))
    (B := C * Real.exp (-a / 4)) (c := (1 / 4 : ℝ)) hat (by norm_num)
    (by positivity) hcont.continuousOn (fun r _ => ?_)
  · rw [stableRescaledSecondDifferential_eq_integral hK hc hm hu hw (ha.trans hat) v w,
      stableRescaledSecondDifferential_eq_integral hK hc hm hu hw ha v w]
    exact H.trans (by convert! HI using 1; dsimp [C]; ring)
  · have heq : C * Real.exp (-r / 4) =
        (C * Real.exp (-a / 4)) * Real.exp (-(1 / 4) * (r - a)) := by
      calc
        C * Real.exp (-r / 4) = C * Real.exp (-a / 4 + -(1 / 4) * (r - a)) := by
          congr 1
          congr 1
          ring
        _ = (C * Real.exp (-a / 4)) * Real.exp (-(1 / 4) * (r - a)) := by
          rw [Real.exp_add]
          ring
    exact heq.le

end BianchiIX
