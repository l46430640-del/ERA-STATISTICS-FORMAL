import BianchiIX.Dynamics.StableInputWeights
import BianchiIX.Dynamics.StableCenterInputGrowth
import BianchiIX.Dynamics.StableSecondStrongDecay

noncomputable section

namespace BianchiIX

theorem stableRescaledSecondDifferential_input_bound {y : StableState} {c s : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| < 1 / 40)
    (hu : |y 1| < 1 / 200) (hw : |y 2| < 1 / 200) (hs : 0 ≤ s) (v w : StableState) :
    ‖stableRescaledSecondDifferential (c + 1) y s v w‖ ≤
      2400000 * Real.exp (512 * (|y 1| + |y 2|)) ^ 3 * stableSecondInputWeight (|y 1| + |y 2|) v w := by
  let vc : StableState := ![v 0, 0, 0]
  let vz : StableState := ![0, v 1, v 2]
  let wc : StableState := ![w 0, 0, 0]
  let wz : StableState := ![0, w 1, w 2]
  let H := stableRescaledSecondDifferential (c + 1) y s
  have hvsum : vc + vz = v := by ext i; fin_cases i <;> simp [vc, vz]
  have hwsum : wc + wz = w := by ext i; fin_cases i <;> simp [wc, wz]
  have hv := stableTangent_split_bounds v
  have hw' := stableTangent_split_bounds w
  have hdecomp : H v w = H vc wc + H vz w + H vc wz := by
    have Hv : H v w = H vc w + H vz w := by rw [← hvsum, map_add, add_apply]
    have Hw : H vc w = H vc wc + H vc wz := by rw [← hwsum, map_add]
    rw [Hv, Hw]
    abel
  have H0 := (stableRescaledSecondDifferential_centerInputs_bound hc hm hu hw hs
    (v := vc) (w := wc) rfl rfl rfl rfl).trans
      (mul_le_mul (mul_le_mul_of_nonneg_left hv.1 (by positivity)) hw'.1 (norm_nonneg _) (by positivity))
  have H1 := (stableRescaledSecondDifferential_bound hc hm hu hw hs vz w).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hv.2.1 (by positivity)) (norm_nonneg w))
  have H2 := (stableRescaledSecondDifferential_bound hc hm hu hw hs vc wz).trans
    (mul_le_mul (mul_le_mul_of_nonneg_left hv.1 (by positivity)) hw'.2.1 (norm_nonneg _) (by positivity))
  change ‖H v w‖ ≤ _
  rw [hdecomp]
  have Htri := (norm_add_le (H vc wc + H vz w) (H vc wz)).trans
    (add_le_add (norm_add_le _ _) (le_refl _))
  have hcross : 0 ≤ Real.exp (512 * (|y 1| + |y 2|)) ^ 3 *
      (‖![v 1, v 2]‖ * ‖w‖ + ‖v‖ * ‖![w 1, w 2]‖) := by positivity
  unfold stableSecondInputWeight
  dsimp only [H] at Htri ⊢
  nlinarith only [Htri, H0, H1, H2, hcross]

theorem stableStrongHessianBudget_input_bound {y : StableState}
    (hb : |y 1| + |y 2| ≤ 1) (v w : StableState) :
    stableStrongHessianBudget y v w ≤ 2 * stableSecondInputWeight (|y 1| + |y 2|) v w := by
  have hv0 : |v 0| ≤ ‖v‖ := norm_le_pi_norm v 0
  have hw0 : |w 0| ≤ ‖w‖ := norm_le_pi_norm w 0
  have hv1 : |v 1| ≤ ‖![v 1, v 2]‖ := norm_le_pi_norm ![v 1, v 2] 0
  have hw1 : |w 1| ≤ ‖![w 1, w 2]‖ := norm_le_pi_norm ![w 1, w 2] 0
  have H0 := mul_le_mul_of_nonneg_right (show |y 1| ≤ |y 1| + |y 2| from le_add_of_nonneg_right (abs_nonneg _))
    (show 0 ≤ ‖v‖ * ‖w‖ by positivity)
  have H1 := mul_le_mul hv0 hw1 (abs_nonneg _) (norm_nonneg _)
  have H2 := mul_le_mul hv1 hw0 (abs_nonneg _) (norm_nonneg _)
  have H3 := mul_le_mul hb (add_le_add (mul_le_mul_of_nonneg_right hv1 (norm_nonneg w))
    (mul_le_mul_of_nonneg_left hw1 (norm_nonneg v))) (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
  unfold stableStrongHessianBudget stableSecondInputWeight
  nlinarith only [H0, H1, H2, H3,
    show 0 ≤ (|y 1| + |y 2|) * ‖v‖ * ‖w‖ by positivity]

end BianchiIX
