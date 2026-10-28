import BianchiIX.Dynamics.RestartSectionMultipliers

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

theorem restartSectionCenterFlow_weak (h T : ℝ) (Z : RestartCenterState) (i : Fin 2) :
    restartSectionCenterFlow h T Z i.succ =
      normalizedMaxCurve (restartSectionChart h Z) 0 T (i.addNat 3) := by
  fin_cases i <;> rfl

/-- Holding an initial weak amplitude fixed preserves that amplitude in the ordinary derivative. -/
theorem exists_restartSectionWeakWall_derivative :
    ∃ C ≥ (32 : ℝ), ∀ h b T : ℝ,
      0 < h → C * h ≤ 1 / 4 → (0 < b ∧ b ≤ 1 / 16) → 0 ≤ T → C * b * T ≤ 1 / 8 →
      ∀ Z : RestartCenterState, ‖Z‖ < b / 2 → ∀ i : Fin 2,
        restartSectionCenterFlow h T Z i.succ = Z i.succ * restartSectionWeakMultiplier h T i Z ∧
        (1 / 2 < restartSectionWeakMultiplier h T i Z ∧ restartSectionWeakMultiplier h T i Z < 2) ∧
        DifferentiableAt ℝ (fun W => restartSectionCenterFlow h T W i.succ) Z ∧
        ∀ v : RestartCenterState, v i.succ = 0 →
          |fderiv ℝ (fun W => restartSectionCenterFlow h T W i.succ) Z v| ≤
            8 * C * T * |restartSectionCenterFlow h T Z i.succ| * ‖v‖ := by
  obtain ⟨C, hC, HC⟩ := exists_restartSectionWeakMultiplier_bounds
  refine ⟨C, hC, ?_⟩
  intro h b T hh hCh hb hT hCb Z hZ i
  obtain ⟨Hformula, _, Hbounds, _, _, Hreg, _, HB⟩ := HC h b T hh hCh hb hT hCb Z hZ.le i
  rw [← restartSectionCenterFlow_weak h T Z i] at Hformula
  have Hnear : ∀ᶠ W : RestartCenterState in 𝓝 Z, ‖W‖ < b / 2 :=
    continuous_norm.continuousAt.eventually (isOpen_Iio.mem_nhds hZ)
  have HE : (fun W => restartSectionCenterFlow h T W i.succ) =ᶠ[𝓝 Z]
      (fun W => W i.succ * restartSectionWeakMultiplier h T i W) := by
    filter_upwards [Hnear] with W hW
    rw [restartSectionCenterFlow_weak]
    exact (HC h b T hh hCh hb hT hCb W hW.le i).1
  have HD := ((hasFDerivAt_apply (𝕜 := ℝ) i.succ Z).mul
    ((Hreg.differentiableAt (by norm_num)).hasFDerivAt)).congr_of_eventuallyEq HE
  have hμ : 0 < restartSectionWeakMultiplier h T i Z := by linarith only [Hbounds.1]
  have Habs : |restartSectionCenterFlow h T Z i.succ| =
      |Z i.succ| * restartSectionWeakMultiplier h T i Z := by
    rw [Hformula, abs_mul, abs_of_pos hμ]
  have HZ : |Z i.succ| ≤ 2 * |restartSectionCenterFlow h T Z i.succ| := by
    nlinarith only [Habs, mul_le_mul_of_nonneg_left Hbounds.1.le (abs_nonneg (Z i.succ))]
  have hC₀ : 0 ≤ C := le_trans (by norm_num : (0 : ℝ) ≤ 32) hC
  refine ⟨Hformula, Hbounds, HD.differentiableAt, ?_⟩
  intro v hv
  rw [HD.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul, ContinuousLinearMap.proj_apply, hv, mul_zero, add_zero]
  have HDμ := ((fderiv ℝ (restartSectionWeakMultiplier h T i) Z).le_opNorm v).trans
    (mul_le_mul_of_nonneg_right HB (norm_nonneg v))
  calc
    _ = |Z i.succ| * |fderiv ℝ (restartSectionWeakMultiplier h T i) Z v| := abs_mul _ _
    _ ≤ (2 * |restartSectionCenterFlow h T Z i.succ|) * ((4 * C * T) * ‖v‖) := by
      exact mul_le_mul HZ HDμ (abs_nonneg _) (by positivity)
    _ = _ := by ring

end BianchiIX
