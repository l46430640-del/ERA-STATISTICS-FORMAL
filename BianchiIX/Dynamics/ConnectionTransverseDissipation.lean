import BianchiIX.Analysis.ConnectionTransverseCoefficients
import BianchiIX.Dynamics.ConnectionPrefix

noncomputable section

namespace BianchiIX

def connectionTransverseBudgetDerivative (μ : ℝ) (y : ProjectiveState) : ℝ :=
  64 * (4 * connectionLogField y 1 +
    2 * y 2 * connectionLogField y 2 / (2 * μ ^ 3) +
    (connectionLogField y 2 * y 3 + y 2 * connectionLogField y 3) / (2 * μ ^ 2))

theorem hasDerivAt_connectionTransverseBudget {Y : ℝ → ProjectiveState} {μ t : ℝ}
    (hY : HasDerivAt Y (connectionLogField (Y t)) t) :
    HasDerivAt (fun s => connectionTransverseBudget μ (Y s 1) (Y s 2) (Y s 3))
      (connectionTransverseBudgetDerivative μ (Y t)) t := by
  have hu := hasDerivAt_pi.mp hY 1
  have hv := hasDerivAt_pi.mp hY 2
  have hw := hasDerivAt_pi.mp hY 3
  convert! (((hu.const_mul 4).add ((hv.pow 2).div_const (2 * μ ^ 3))).add
    ((hv.mul hw).div_const (2 * μ ^ 2))).const_mul 64 using 1
  simp only [connectionTransverseBudgetDerivative, Nat.cast_ofNat, Nat.reduceSub, pow_one]

theorem connectionTransverseBudget_dissipation {μ : ℝ} {y : ProjectiveState} (hμ : 4 ≤ μ)
    (hm : |-y 0 - μ| ≤ 1 / 2) (hu : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000)
    (hv : 0 ≤ y 2 ∧ y 2 ≤ 1) (hw : 0 ≤ y 3 ∧ y 3 ≤ 1) (huv : y 1 ≤ y 2) :
    connectionTransverseBudgetDerivative μ y ≤ -connectionTransverseRate μ (y 1) (y 2) (y 3) := by
  have hμ0 : 0 < μ := by linarith only [hμ]
  have hv0 := hv.1
  have hD : 0 < connectionClockRate y := by
    have H := (connection_speed_bounds hμ hm hu hv hw).1
    change μ / 2 ≤ connectionClockRate y at H
    linarith only [H, hμ]
  have hfield := connectionLogField_components (ne_of_gt hD)
  have hU : connectionLogField y 1 ≤ -μ / 2 * y 1 := by
    rw [hfield.2.1]
    exact mul_le_mul_of_nonneg_right (connection_strong_clock_rate_le hμ hm hu hv hw huv) hu.1
  have hweak := connection_weak_clock_rates hμ hm hu hv hw huv
  have hV : connectionLogField y 2 ≤ -y 2 := by
    rw [hfield.2.2.1]
    have H := mul_le_mul_of_nonneg_right hweak.1 hv.1
    simp only [neg_neg] at H
    have H' : 0 ≤ (2 / μ) * y 2 := mul_nonneg (by positivity) hv.1
    change (y 0 - 1 - coupling (y 1) (y 2) (y 3)) / connectionClockRate y * y 2 ≤ _ at H
    linarith only [H, H']
  have hP : connectionLogField y 2 * y 3 + y 2 * connectionLogField y 3 ≤
      -2 / μ * (y 2 * y 3) := by
    have hid : connectionLogField y 2 * y 3 + y 2 * connectionLogField y 3 =
        (-2 * (1 + coupling (y 1) (y 2) (y 3)) / connectionClockRate y) * (y 2 * y 3) := by
      rw [hfield.2.2.1, hfield.2.2.2]
      dsimp [connectionClockRate, connectionSpeed] at *
      field_simp
      ring
    rw [hid]
    exact mul_le_mul_of_nonneg_right hweak.2 (mul_nonneg hv.1 hw.1)
  have H := add_le_add (add_le_add (mul_le_mul_of_nonneg_left hU (by norm_num : (0 : ℝ) ≤ 4))
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hV (by positivity : 0 ≤ 2 * y 2))
      (by positivity : 0 ≤ 2 * μ ^ 3)))
    (div_le_div_of_nonneg_right hP (by positivity : 0 ≤ 2 * μ ^ 2))
  apply (mul_le_mul_of_nonneg_left H (by norm_num : (0 : ℝ) ≤ 64)).trans_eq
  dsimp [connectionTransverseRate]
  field_simp
  ring

end BianchiIX
