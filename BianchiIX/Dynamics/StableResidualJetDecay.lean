import BianchiIX.Dynamics.StableInputWeights

noncomputable section

namespace BianchiIX

theorem stableResidualFirstDecay_bound {Y a v : StableState} {b E q : ℝ}
    (hb : 0 ≤ b) (hE : 0 ≤ E) (hq : 0 ≤ q)
    (hY : |Y 1| + |Y 2| ≤ b) (hU : |Y 1| ≤ b * q)
    (ha : ‖a‖ ≤ E * ‖v‖) (haz : ‖![a 1, a 2]‖ ≤ 256 * E * stableFirstInputWeight b v)
    (haU : |a 1| ≤ 200 * E * stableFirstInputWeight b v * q) :
    |a 1| * (|Y 1| + |Y 2|) ^ 3 + |Y 1| * stableCubicFirstBudget Y a ≤
      969 * E * b ^ 3 * stableFirstInputWeight b v * q := by
  have hA := stableFirstInputWeight_nonneg hb v
  have h3 := pow_le_pow_left₀ (by positivity : 0 ≤ |Y 1| + |Y 2|) hY 3
  have H0 := mul_le_mul haU h3 (by positivity) (by positivity : 0 ≤ 200 * E * stableFirstInputWeight b v * q)
  have H1 := mul_le_mul hU (stableCubicFirstBudget_weighted hb hE hY ha haz)
    (stableCubicFirstBudget_nonneg Y a) (mul_nonneg hb hq)
  nlinarith only [H0, H1]

theorem stableResidualSecondDecay_bound {Y a d h v w : StableState} {b E q : ℝ}
    (hb : 0 ≤ b) (hb1 : b ≤ 1) (hE : 1 ≤ E) (hq : 0 ≤ q)
    (hY : |Y 1| + |Y 2| ≤ b) (hU : |Y 1| ≤ b * q)
    (ha : ‖a‖ ≤ E * ‖v‖) (hd : ‖d‖ ≤ E * ‖w‖)
    (haz : ‖![a 1, a 2]‖ ≤ 256 * E * stableFirstInputWeight b v)
    (hdz : ‖![d 1, d 2]‖ ≤ 256 * E * stableFirstInputWeight b w)
    (haU : |a 1| ≤ 200 * E * stableFirstInputWeight b v * q)
    (hdU : |d 1| ≤ 200 * E * stableFirstInputWeight b w * q)
    (hh : ‖h‖ ≤ 2400000 * E ^ 3 * stableSecondInputWeight b v w)
    (hhU : |h 1| ≤ 320000000 * E ^ 3 * stableSecondInputWeight b v w * q) :
    |h 1| * (|Y 1| + |Y 2|) ^ 3 + |Y 1| * stableCubicFirstBudget Y h +
      |a 1| * stableCubicFirstBudget Y d + |d 1| * stableCubicFirstBudget Y a +
      |Y 1| * stableCubicSecondBudget Y a d ≤
      400000000 * E ^ 3 * b ^ 2 * stableFirstInputWeight b v * stableFirstInputWeight b w * q := by
  have hE0 : 0 ≤ E := le_trans (by norm_num) hE
  have hA := stableFirstInputWeight_nonneg hb v
  have hB := stableFirstInputWeight_nonneg hb w
  have hW := stableSecondInputWeight_nonneg hb v w
  have h3 := pow_le_pow_left₀ (by positivity : 0 ≤ |Y 1| + |Y 2|) hY 3
  have H0 := mul_le_mul hhU h3 (by positivity)
    (by positivity : 0 ≤ 320000000 * E ^ 3 * stableSecondInputWeight b v w * q)
  have Hh := (stableCubicFirstBudget_norm hb1 hY (a := h)).trans
    (mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ 4 * b ^ 2))
  have H1 := mul_le_mul hU Hh (stableCubicFirstBudget_nonneg Y h) (mul_nonneg hb hq)
  have H2 := mul_le_mul haU (stableCubicFirstBudget_weighted hb hE0 hY hd hdz)
    (stableCubicFirstBudget_nonneg Y d) (by positivity : 0 ≤ 200 * E * stableFirstInputWeight b v * q)
  have H3 := mul_le_mul hdU (stableCubicFirstBudget_weighted hb hE0 hY ha haz)
    (stableCubicFirstBudget_nonneg Y a) (by positivity : 0 ≤ 200 * E * stableFirstInputWeight b w * q)
  have H4 := mul_le_mul hU (stableCubicSecondBudget_weighted hb hE0 hY ha hd haz hdz)
    (stableCubicSecondBudget_nonneg Y a d) (mul_nonneg hb hq)
  have TW := mul_le_mul_of_nonneg_left (stableSecondInputWeight_product b v w)
    (show 0 ≤ E ^ 3 * b ^ 2 * q by positivity)
  have TE := mul_le_mul_of_nonneg_right (show E ^ 2 ≤ E ^ 3 by nlinarith [sq_nonneg E])
    (show 0 ≤ b ^ 2 * stableFirstInputWeight b v * stableFirstInputWeight b w * q by positivity)
  have Tpos : 0 ≤ E ^ 3 * b ^ 2 * stableFirstInputWeight b v * stableFirstInputWeight b w * q := by positivity
  nlinarith only [H0, H1, H2, H3, H4, TW, TE, Tpos]

end BianchiIX
