import BianchiIX.Dynamics.ConnectionReturnPhaseBoundary
import BianchiIX.Analysis.ThreeCoordinateLinear
import BianchiIX.Algebra.PartialCoreConnectionBudget

noncomputable section

namespace BianchiIX

/-- The actual phase correction along a curve, with amplitude-preserving radial bounds. -/
theorem connectionReturn_phase_curve_bounds {p : ℝ → ConnectionParameters}
    {v : ConnectionParameters} {x r K M A B U P : ℝ}
    (hp : HasDerivAt p v x) (hr : 0 < r) (hK : 0 ≤ K)
    (hM : 0 ≤ M) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hμ : 4 ≤ p x 0) (hi : 1 / p x 0 ≤ K * r)
    (hu : 0 ≤ p x 1 ∧ p x 1 ≤ (1 / 10000) / p x 0)
    (hw : 0 < p x 2 ∧ p x 2 ≤ 1 / 10000)
    (hU : 0 ≤ U) (hP : 0 ≤ P ∧ P ≤ 1) (huU : p x 1 ≤ U) (hwP : p x 2 ≤ P)
    (hv0 : |v 0| ≤ M / r ^ 2) (hv1 : r * |v 1| ≤ A * U) (hv2 : r * |v 2| ≤ B * P) :
    DifferentiableAt ℝ (fun a => connectionReturnPhaseError (p a)) x ∧
      |connectionReturnPhaseError (p x)| ≤ 24 * K * r * (U + P ^ 2) ∧
      |deriv (fun a => connectionReturnPhaseError (p a)) x| ≤
        50000 * (K ^ 2 * M + K * A + K * B) * (U + P ^ 2) := by
  have hw0 := hw.1.le
  have Hreg := (contDiffAt_connectionReturnPhaseError hμ hu hw).differentiableAt (by norm_num)
  have HD := Hreg.hasFDerivAt.comp_hasDerivAt (f := p) x hp
  dsimp only [Function.comp_def] at HD
  have Hcols := connectionReturn_phase_response_bounds_nonneg hμ hu hw
  have Hlinear := three_coordinate_linear_bound (fderiv ℝ connectionReturnPhaseError (p x)) v
  have Hbound := Hlinear.trans (add_le_add
    (add_le_add (mul_le_mul_of_nonneg_left Hcols.1 (abs_nonneg _))
      (mul_le_mul_of_nonneg_left Hcols.2.1 (abs_nonneg _)))
    (mul_le_mul_of_nonneg_left Hcols.2.2 (abs_nonneg _)))
  refine ⟨HD.differentiableAt, ?_, ?_⟩
  · calc
      _ ≤ 24 * (p x 1 + (p x 2) ^ 2) / p x 0 := connectionReturn_phase_bound hμ hu hw
      _ = 24 * (p x 1 + (p x 2) ^ 2) * (1 / p x 0) := by ring
      _ ≤ 24 * (U + P ^ 2) * (K * r) := by gcongr
      _ = _ := by ring
  · rw [HD.deriv]
    exact Hbound.trans (connection_phase_radial_budget hr hK hM hA hB
      (by linarith only [hμ]) hi hU hP ⟨hu.1, huU⟩ ⟨hw.1.le, hwP⟩ hv0 hv1 hv2)

end BianchiIX
