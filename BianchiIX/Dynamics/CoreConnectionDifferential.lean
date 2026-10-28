import BianchiIX.Dynamics.CoreReflection

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

/-- Changing the radial coordinate preserves the physical phase differential exactly. -/
theorem coreExitConnectionParameters_differential {Z : CoreAngleState} (hK : 1 < Z 0)
    (v : CoreAngleState) :
    let p := coreExitConnectionParameters Z
    let w := fderiv ℝ coreExitConnectionParameters Z v
    ((p 0 + 1) / phaseNorm (p 0 + 1) 1) * w 0 = v 0 ∧ w 1 = v 1 ∧ w 2 = v 2 := by
  intro p w
  have hc := (contDiffAt_coreExitConnectionParameters 1 hK).differentiableAt (by norm_num)
  have heq : (fun X => phaseNorm (coreExitConnectionParameters X 0 + 1) 1) =ᶠ[𝓝 Z]
      (fun X : CoreAngleState => X 0) := by
    filter_upwards [(continuous_apply 0).continuousAt.eventually (lt_mem_nhds hK)] with X hX
    exact coreExitConnectionParameters_phase hX
  have H := (hasFDerivAt_connectionEntrancePhase p).comp Z hc.hasFDerivAt
  have He := (H.congr_of_eventuallyEq heq.symm).unique (hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 3) Z)
  have Hphase := congrArg (fun A : CoreAngleState →L[ℝ] ℝ => A v) He
  have hcomponent (i : Fin 2) : w i.succ = v i.succ := by
    have Hi : HasFDerivAt (fun X => coreExitConnectionParameters X i.succ)
        (ContinuousLinearMap.proj i.succ : CoreAngleState →L[ℝ] ℝ) Z := by
      fin_cases i <;> exact hasFDerivAt_apply _ _
    have Hd := Hi.fderiv
    rw [fderiv_apply hc i.succ] at Hd
    exact congrArg (fun A : CoreAngleState →L[ℝ] ℝ => A v) Hd
  exact ⟨Hphase, hcomponent 0, hcomponent 1⟩

theorem coreConnectionParameters_differential {Y : CoreAngleState} {τ : CoreAngleState → ℝ}
    (hK : 1 < coreReturnState τ Y 0) (hcore : DifferentiableAt ℝ (coreReturnState τ) Y)
    (v : CoreAngleState) :
    let p := coreConnectionParameters τ Y
    let ξ := fderiv ℝ (coreReturnState τ) Y v
    let w := fderiv ℝ (coreConnectionParameters τ) Y v
    ((p 0 + 1) / phaseNorm (p 0 + 1) 1) * w 0 = ξ 0 ∧ w 1 = ξ 1 ∧ w 2 = ξ 2 := by
  intro p ξ w
  have hc := (contDiffAt_coreExitConnectionParameters 1 hK).differentiableAt (by norm_num)
  have hw : w = fderiv ℝ coreExitConnectionParameters (coreReturnState τ Y) ξ := by
    change fderiv ℝ (coreExitConnectionParameters ∘ coreReturnState τ) Y v = _
    rw [fderiv_comp Y hc hcore, ContinuousLinearMap.comp_apply]
  rw [hw]
  exact coreExitConnectionParameters_differential hK ξ

end BianchiIX
