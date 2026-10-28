import BianchiIX.Analysis.ConnectionWeightedVariation

noncomputable section

namespace BianchiIX

def connectionWallForcingEnvelope (μ : ℝ) (y : ProjectiveState) : ℝ :=
  64 * ((y 3 ^ 2 + y 2 * y 3) / μ + μ * y 1 * y 3)

theorem continuous_connectionWallForcingEnvelope (μ : ℝ) :
    Continuous (connectionWallForcingEnvelope μ) := by
  unfold connectionWallForcingEnvelope
  fun_prop

theorem connectionWallColumn_norm {μ : ℝ} {y : ProjectiveState} (hμ : 4 ≤ μ)
    (hm : |-y 0 - μ| ≤ 1 / 2) (hu : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000)
    (hv : 0 ≤ y 2 ∧ y 2 ≤ 1) (hw : 0 ≤ y 3 ∧ y 3 ≤ 1) :
    ‖connectionWallColumn μ y‖ ≤ connectionWallForcingEnvelope μ y := by
  have hμ0 : 0 < μ := by linarith only [hμ]
  have huw : 0 ≤ y 1 * y 3 := mul_nonneg hu.1 hw.1
  have hvw : 0 ≤ y 2 * y 3 / μ := div_nonneg (mul_nonneg hv.1 hw.1) hμ0.le
  have hbase : 0 ≤ (y 3 ^ 2 + y 2 * y 3) / μ :=
    div_nonneg (add_nonneg (sq_nonneg _) (mul_nonneg hv.1 hw.1)) hμ0.le
  have hmul : y 1 * y 3 ≤ μ * y 1 * y 3 := by nlinarith only [hμ, huw]
  apply (pi_norm_le_iff_of_nonempty _).mpr
  intro i
  fin_cases i
  · change ‖connectionStrongClockPartials (-y 0) (y 1) (y 2) (y 3) 3‖ ≤ _
    rw [Real.norm_eq_abs]
    apply (connectionStrongClockPartials_bounds hμ hm hu hv hw).2.2.2.trans
    dsimp [connectionWallForcingEnvelope]
    nlinarith only [hbase, huw, hmul]
  · change ‖μ ^ 2 * connectionWeakClockPartials (-y 0) (y 1) (y 2) (y 3) 3‖ ≤ _
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg μ)]
    apply (mul_le_mul_of_nonneg_left (connectionWeakClockPartials_bounds hμ hm hu hv hw).2.2.2
      (sq_nonneg μ)).trans
    have hid : μ ^ 2 * (64 * (y 3 ^ 2 / μ ^ 3 + y 1 * y 3 / μ)) =
        64 * (y 3 ^ 2 / μ + μ * y 1 * y 3) := by field_simp
    rw [hid]
    dsimp [connectionWallForcingEnvelope]
    rw [add_div]
    linarith only [hvw]

theorem connectionWeighted_forcing_bound {μ : ℝ} {y : ProjectiveState} (hμ : 4 ≤ μ)
    (hm : |-y 0 - μ| ≤ 1 / 2) (hu : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000)
    (hv : 0 ≤ y 2 ∧ y 2 ≤ 1) (hw : 0 ≤ y 3 ∧ y 3 ≤ 1) (Z ζ : ℝ) :
    ‖Z • connectionPhaseColumn μ y + ζ • connectionWallColumn μ y‖ ≤
      64 * |Z| + |ζ| * connectionWallForcingEnvelope μ y := by
  apply (norm_add_le _ _).trans
  apply add_le_add (connectionPhaseColumn_forcing hμ hm hu hv hw Z)
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (connectionWallColumn_norm hμ hm hu hv hw) (abs_nonneg ζ)

end BianchiIX
