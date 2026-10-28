import BianchiIX.Analysis.ConnectionForcingBounds

noncomputable section

namespace BianchiIX

def connectionGrowingStrongSource (μ w : ℝ) (y : ProjectiveState) : ℝ :=
  32 * ((y 3 ^ 2 + y 2 * y 3) / μ + y 1 * y 3) / w

def connectionGrowingWeakSource (μ w : ℝ) (y : ProjectiveState) : ℝ :=
  64 * (y 3 ^ 2 / μ + μ * y 1 * y 3) / w

def connectionGrowingPhaseSource (μ w : ℝ) (y : ProjectiveState) : ℝ :=
  32 * (y 1 * y 3 + (y 2 * y 3) ^ 2 / μ ^ 3) / w

theorem continuous_connectionGrowingSources (μ w : ℝ) :
    Continuous (connectionGrowingStrongSource μ w) ∧ Continuous (connectionGrowingWeakSource μ w) ∧
      Continuous (connectionGrowingPhaseSource μ w) := by
  unfold connectionGrowingStrongSource connectionGrowingWeakSource connectionGrowingPhaseSource
  exact ⟨by fun_prop, by fun_prop, by fun_prop⟩

theorem connectionGrowingSources_nonneg {μ w : ℝ} {y : ProjectiveState}
    (hμ : 0 ≤ μ) (hw : 0 ≤ w) (hu : 0 ≤ y 1) (hv : 0 ≤ y 2) (hW : 0 ≤ y 3) :
    0 ≤ connectionGrowingStrongSource μ w y ∧ 0 ≤ connectionGrowingWeakSource μ w y ∧
      0 ≤ connectionGrowingPhaseSource μ w y := by
  unfold connectionGrowingStrongSource connectionGrowingWeakSource connectionGrowingPhaseSource
  exact ⟨by positivity, by positivity, by positivity⟩

theorem connectionGrowingSources_bound {μ w : ℝ} {y : ProjectiveState} (hμ : 4 ≤ μ) (hw0 : 0 < w)
    (hm : |-y 0 - μ| ≤ 1 / 2) (hu : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000)
    (hv : 0 ≤ y 2 ∧ y 2 ≤ 1) (hw : 0 ≤ y 3 ∧ y 3 ≤ 1) :
    |connectionStrongClockPartials (-y 0) (y 1) (y 2) (y 3) 3 / w| ≤ connectionGrowingStrongSource μ w y ∧
      |μ ^ 2 * connectionWeakClockPartials (-y 0) (y 1) (y 2) (y 3) 3 / w| ≤ connectionGrowingWeakSource μ w y ∧
      |connectionPhaseGPartials (-y 0) (y 1) (y 2) (y 3) 3 / w| ≤ connectionGrowingPhaseSource μ w y := by
  have hμ0 : 0 < μ := by linarith only [hμ]
  simp only [abs_div, abs_of_pos hw0]
  refine ⟨div_le_div_of_nonneg_right (connectionStrongClockPartials_bounds hμ hm hu hv hw).2.2.2 hw0.le,
    ?_, div_le_div_of_nonneg_right (connectionPhaseGPartials_bounds hμ hm hu hv hw).2.2.2 hw0.le⟩
  rw [abs_mul, abs_of_nonneg (sq_nonneg μ)]
  apply (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (connectionWeakClockPartials_bounds hμ hm hu hv hw).2.2.2 (sq_nonneg μ)) hw0.le).trans_eq
  unfold connectionGrowingWeakSource
  field_simp

end BianchiIX
