import BianchiIX.Dynamics.StableSecondCenterForcing

noncomputable section

namespace BianchiIX

theorem stableRescaledSecondSource_center_of_bounds {y v w : StableState} {c s M Q : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 40)
    (hu : |y 1| ≤ 1 / 200) (hw : |y 2| ≤ 1 / 200) (hs : 0 ≤ s) (hM : 0 ≤ M)
    (hH : ‖stableRescaledSecondDifferential (c + 1) y s v w‖ ≤ M)
    (hq : |((c + 1) • stableOriginalHessian (stableRescaledFlow (c + 1) y s)
      (stableRescaledDifferential (c + 1) y s v) (stableRescaledDifferential (c + 1) y s w)) 0| ≤
        Q * Real.exp (-s / 4)) :
    |stableRescaledSecondSource (c + 1) v w (y, s) 0| ≤
      (192 * (|y 1| + |y 2|) * M + Q) * Real.exp (-s / 4) := by
  let b := |y 1| + |y 2|
  let Y := stableRescaledFlow (c + 1) y s
  let H := stableRescaledSecondDifferential (c + 1) y s v w
  let B := |Y 1| + |Y 2|
  let q := (c + 1) • stableOriginalHessian Y
    (stableRescaledDifferential (c + 1) y s v) (stableRescaledDifferential (c + 1) y s w)
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  obtain ⟨hm', hu', hw'⟩ := stableRescaledFlow_band hc hm hu hw hs
  have hB1 : B ≤ 1 := by dsimp [B, Y]; linarith
  have hH0 : |H 0| ≤ M :=
    (show |H 0| ≤ ‖H‖ by simpa only [Real.norm_eq_abs] using norm_le_pi_norm H 0).trans hH
  have hHz : ‖![H 1, H 2]‖ ≤ M := (stableTangent_split_bounds H).2.2.trans hH
  have hBdec : B ≤ b * Real.exp (-s / 4) :=
    (stableRescaledFlow_amplitude_decay hc hm hu hw hs).trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith : -s / 2 ≤ -s / 4)) hb)
  have hlinear : |(c + 1) * (stableOriginalJacobian Y).mulVec H 0| ≤
      192 * b * M * Real.exp (-s / 4) := by
    have H0 := stableRescaledJacobian_center_apply (v := H) hc hm' hu' hw'
    have H1 := mul_le_mul_of_nonneg_left hH0 (show 0 ≤ 64 * B ^ 2 by positivity)
    have H2 := mul_le_mul_of_nonneg_left hHz (show 0 ≤ 128 * B by positivity)
    have H3 := mul_le_mul_of_nonneg_right (show B ^ 2 ≤ B by nlinarith) hM
    have H4 := mul_le_mul_of_nonneg_right hBdec hM
    nlinarith only [H0, H1, H2, H3, H4]
  have heq : stableRescaledSecondSource (c + 1) v w (y, s) 0 =
      q 0 + (c + 1) * (stableOriginalJacobian Y).mulVec H 0 := by
    dsimp [stableRescaledSecondSource, q, Y, H]
    ring
  rw [heq]
  have Hsum := (abs_add_le _ _).trans (add_le_add hq hlinear)
  convert! Hsum using 1
  dsimp [b]
  ring

theorem stableRescaledSecondSource_centerInputs_rate {y v w : StableState} {c s : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| < 1 / 40)
    (hu : |y 1| < 1 / 200) (hw : |y 2| < 1 / 200) (hs : 0 ≤ s)
    (hv1 : v 1 = 0) (hv2 : v 2 = 0) (hw1 : w 1 = 0) (hw2 : w 2 = 0) :
    |stableRescaledSecondSource (c + 1) v w (y, s) 0| ≤
      600000000 * (|y 1| + |y 2|) ^ 2 * Real.exp (512 * (|y 1| + |y 2|)) ^ 3 *
        ‖v‖ * ‖w‖ * Real.exp (-s / 4) := by
  let b := |y 1| + |y 2|
  let E := Real.exp (512 * b)
  have hE : 1 ≤ E := Real.one_le_exp (by dsimp [b]; positivity)
  have H := stableRescaledSecondSource_center_of_bounds hc hm.le hu.le hw.le hs (by positivity)
    (stableRescaledSecondDifferential_centerInputs_bound hc hm hu hw hs hv1 hv2 hw1 hw2)
    (stableSecondCenterForcing_centerInputs hc hm.le hu.le hw.le hs hv1 hv2 hw1 hw2)
  have HE := mul_le_mul_of_nonneg_right (show E ^ 2 ≤ E ^ 3 by nlinarith [sq_nonneg E])
    (show 0 ≤ b ^ 2 * ‖v‖ * ‖w‖ * Real.exp (-s / 4) by positivity)
  have hn : 0 ≤ b ^ 2 * E ^ 3 * ‖v‖ * ‖w‖ * Real.exp (-s / 4) := by positivity
  change _ ≤ 600000000 * b ^ 2 * E ^ 3 * ‖v‖ * ‖w‖ * Real.exp (-s / 4)
  nlinarith only [H, HE, hn]

theorem stableRescaledSecondSource_centerInput_rate {y v w : StableState} {c s : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| < 1 / 40)
    (hu : |y 1| < 1 / 200) (hw : |y 2| < 1 / 200) (hs : 0 ≤ s)
    (hv1 : v 1 = 0) (hv2 : v 2 = 0) :
    |stableRescaledSecondSource (c + 1) v w (y, s) 0| ≤
      10000000 * (|y 1| + |y 2|) * Real.exp (512 * (|y 1| + |y 2|)) ^ 3 *
        ‖v‖ * ‖w‖ * Real.exp (-s / 4) := by
  let b := |y 1| + |y 2|
  let E := Real.exp (512 * b)
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hE : 1 ≤ E := Real.one_le_exp (by positivity)
  have H := stableRescaledSecondSource_center_of_bounds hc hm.le hu.le hw.le hs (by positivity)
    (stableRescaledSecondDifferential_bound hc hm hu hw hs v w)
    (stableSecondCenterForcing_centerInput hc hm.le hu.le hw.le hs hv1 hv2)
  have HE := mul_le_mul_of_nonneg_right (show E ^ 2 ≤ E ^ 3 by nlinarith [sq_nonneg E])
    (show 0 ≤ b * ‖v‖ * ‖w‖ * Real.exp (-s / 4) by positivity)
  have hn : 0 ≤ b * E ^ 3 * ‖v‖ * ‖w‖ * Real.exp (-s / 4) := by positivity
  change _ ≤ 10000000 * b * E ^ 3 * ‖v‖ * ‖w‖ * Real.exp (-s / 4)
  nlinarith only [H, HE, hn]

end BianchiIX
