import BianchiIX.Dynamics.CoreMultiplierContraction

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

def coreReturnState (τ : CoreAngleState → ℝ) (Y : CoreAngleState) : CoreAngleState :=
  toCoreAngleState (projectiveOriginalFlow (coreRadiusEntry Y) 0 (τ Y))

/-- First-return uniqueness identifies the radial estimate for any chosen local return branch. -/
theorem coreReturnState_radius_bound {Y : CoreAngleState} {τ : CoreAngleState → ℝ}
    (hk : 6 ≤ Y 0) (hu : 0 ≤ Y 1 ∧ Y 1 ≤ (1 / 10000) / Y 0)
    (hw : 0 ≤ Y 2 ∧ Y 2 ≤ (1 / 10000) / Y 0)
    (hnear : ∀ᶠ Z in 𝓝 Y,
      IsLeast {t | 0 < t ∧ projectiveOriginalFlow (coreRadiusEntry Z) 0 t 2 = 1} (τ Z)) :
    ContDiffAt ℝ 1 (coreReturnState τ) Y ∧ ∀ v : CoreAngleState,
      |(fderiv ℝ (coreReturnState τ) Y v) 0 - v 0| ≤ (1040 + 512 * coreVariationBound) *
        (|v 1| / Y 0 + (Y 1 + Y 2) * (|v 0| + Y 0 * |v 1| + |v 2|) / Y 0) := by
  obtain ⟨_, _, _, σ, _, _, hσ, hcF, hbound⟩ := exists_large_core_radius_arrival hk hu hw
  have heq : coreReturnState τ =ᶠ[𝓝 Y] coreReturnState σ := by
    filter_upwards [hnear, hσ] with Z hZ hσZ
    unfold coreReturnState
    rw [hZ.unique hσZ.1]
  exact ⟨hcF.congr_of_eventuallyEq heq, fun v => by rw [heq.fderiv_eq]; exact hbound v⟩

theorem coreReturnState_multiplier_formula {Y : CoreAngleState} {τ : CoreAngleState → ℝ}
    (hnear : ∀ᶠ Z in 𝓝 Y,
      projectiveOriginalFlow (coreRadiusEntry Z) 0 (τ Z) 2 = 1 ∧
      projectiveOriginalFlow (coreRadiusEntry Z) 0 (τ Z) 1 = Z 1 * coreReturnMultiplier τ Z 0 ∧
      projectiveOriginalFlow (coreRadiusEntry Z) 0 (τ Z) 3 = Z 2 * coreReturnMultiplier τ Z 1)
    (i : Fin 2) :
    (fun Z => coreReturnState τ Z i.succ) =ᶠ[𝓝 Y]
      (fun Z => Z i.succ * coreReturnMultiplier τ Z i) := by
  filter_upwards [hnear] with Z hZ
  fin_cases i
  · exact hZ.2.1
  · change projectiveOriginalFlow (coreRadiusEntry Z) 0 (τ Z) 2 *
        projectiveOriginalFlow (coreRadiusEntry Z) 0 (τ Z) 3 = _
    rw [hZ.1, one_mul, hZ.2.2]
    rfl

/-- Differentiate the actual amplitude product without dividing by an input wall. -/
theorem coreReturnState_transverse_differential {Y : CoreAngleState} {τ : CoreAngleState → ℝ}
    (hF : DifferentiableAt ℝ (coreReturnState τ) Y)
    (hnear : ∀ᶠ Z in 𝓝 Y,
      projectiveOriginalFlow (coreRadiusEntry Z) 0 (τ Z) 2 = 1 ∧
      projectiveOriginalFlow (coreRadiusEntry Z) 0 (τ Z) 1 = Z 1 * coreReturnMultiplier τ Z 0 ∧
      projectiveOriginalFlow (coreRadiusEntry Z) 0 (τ Z) 3 = Z 2 * coreReturnMultiplier τ Z 1)
    (i : Fin 2) (hlog : DifferentiableAt ℝ (fun Z => Real.log (coreReturnMultiplier τ Z i)) Y)
    (v : CoreAngleState) :
    (fderiv ℝ (coreReturnState τ) Y v) i.succ = coreReturnMultiplier τ Y i *
      (v i.succ + Y i.succ * fderiv ℝ (fun Z => Real.log (coreReturnMultiplier τ Z i)) Y v) := by
  have hm : HasFDerivAt (fun Z => coreReturnMultiplier τ Z i)
      (coreReturnMultiplier τ Y i • fderiv ℝ (fun Z => Real.log (coreReturnMultiplier τ Z i)) Y) Y := by
    convert! hlog.hasFDerivAt.exp using 1
    · ext Z
      exact (Real.exp_log (coreFlowMultiplier_pos _ _ _ _ i)).symm
    · rw [Real.exp_log (show 0 < coreReturnMultiplier τ Y i from coreFlowMultiplier_pos _ _ _ _ i)]
  have hprod := (hasFDerivAt_apply (𝕜 := ℝ) i.succ Y).mul hm
  change HasFDerivAt (fun Z => Z i.succ * coreReturnMultiplier τ Z i) _ Y at hprod
  have H := congrArg (fun L : CoreAngleState →L[ℝ] ℝ => L v)
    ((coreReturnState_multiplier_formula hnear i).fderiv_eq.trans hprod.fderiv)
  rw [fderiv_apply hF i.succ] at H
  convert! H using 1
  simp only [add_apply, smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
  ring

end BianchiIX
