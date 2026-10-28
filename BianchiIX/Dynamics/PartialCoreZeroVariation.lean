import BianchiIX.Dynamics.PartialCoreLogDerivativeBounds

noncomputable section

namespace BianchiIX

open Set Filter MeasureTheory
open scoped Topology

theorem coreLogRates_zero_walls (k z : ℝ) :
    coreLogRates z ![k, 0, 0] = ![Real.tanh z - k / 2, -2 / k] := by
  ext i
  fin_cases i <;> simp [coreLogRates, coreAuxiliary, coreClockFactor, coupling]
  ring

/-- A vanishing fixed-angle variation leaves only the moving initial endpoint. -/
theorem partialCoreReturn_log_derivative_of_zero_variation {k : ℝ} {y : ProjectiveState}
    {τ : ProjectiveState → ℝ} (hk : 6 ≤ k) (hD : 0 < projectiveStateDenom y)
    (hτ : ContDiffAt ℝ 1 τ y) (hpos : 0 ≤ τ y)
    (hdom : Icc 0 (τ y) ⊆ normalizedMaxDomain (fromProjectiveState y) 0)
    (hA : ∀ t ∈ Icc 0 (τ y), 0 < 1 + normalizedMaxCurve (fromProjectiveState y) 0 t 0)
    (hcore : ∀ t ∈ Icc 0 (τ y), coreRegion k (projectiveOriginalFlow y 0 t))
    (hhit : ∀ᶠ x in 𝓝 y, projectiveOriginalFlow x 0 (τ x) 2 = 1)
    (hM : projectiveOriginalFlow y 0 (τ y) 0 < 1) (w : ProjectiveState)
    (hzero : ∀ t ∈ Icc 0 (τ y), coreProjectedFlowVariation y 0 t w = 0) (i : Fin 2) :
    fderiv ℝ (fun x => Real.log (partialCoreReturnMultiplier τ x i)) y w =
      -coreLogRates (projectiveCoreAngle y) (toCoreAngleState y) i *
        fderiv ℝ projectiveCoreAngle y w := by
  have hend : τ y ∈ Icc 0 (τ y) := ⟨hpos, le_rfl⟩
  have H := partialCoreReturn_exit_angle_bound hk hD hτ.continuousAt (hdom hend)
    (hA _ hend) (hcore _ hend) hhit hM w
  rw [hzero _ hend] at H
  simp only [Pi.zero_apply, abs_zero, mul_zero, zero_div, abs_nonpos_iff] at H
  rw [partialCoreReturn_log_derivative hk hD hτ hpos hdom hA hcore w i, H]
  have hI : (∫ t in 0..τ y, coreOriginalClockRate (projectiveOriginalFlow y 0 t) *
      (fderiv ℝ (coreLogRates (projectiveCoreAngle (projectiveOriginalFlow y 0 t)))
        (toCoreAngleState (projectiveOriginalFlow y 0 t)) (coreProjectedFlowVariation y 0 t w)) i) = 0 := by
    calc
      _ = ∫ _t in 0..τ y, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        dsimp only
        rw [hzero t (uIcc_of_le hpos ▸ ht), map_zero]
        simp
      _ = 0 := by simp
  rw [hI]
  dsimp only
  rw [projectiveOriginalFlow_initial hD]
  ring

end BianchiIX
