import BianchiIX.Dynamics.ConnectionReturn

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

/-- The canonical return derivative includes the variation of the actual arrival time. -/
theorem connectionReturn_differential {p : ConnectionParameters} (hμ : 4 ≤ p 0)
    (hu : 0 ≤ p 1 ∧ p 1 ≤ (1 / 10000) / p 0) (hw : 0 < p 2 ∧ p 2 ≤ 1 / 10000)
    (v : ConnectionParameters) :
    let x := connectionInitialState p
    let T := connectionReturnTime p
    let y := normalizedMaxCurve x 0 T
    let ξ := fderiv ℝ toProjectiveState y (normalizedFlowDifferential x 0 T (fderiv ℝ connectionInitialState p v))
    fderiv ℝ connectionReturnTime p v = -(normalizedEventRate projectiveGrowingWall x 0 T)⁻¹ * ξ 3 ∧
      fderiv ℝ connectionReturnState p v =
        ξ - (ξ 3 / projectiveField (connectionReturnState p) 3) • projectiveField (connectionReturnState p) := by
  intro x T y ξ
  have H := connectionReturn_regular hμ hu hw
  have hvalid := H.1
  have htime := H.2.2.2.1
  have hstate := H.2.2.2.2.1
  have hA : 1 + y 0 ≠ 0 := ne_of_gt (hvalid.2.1 T ⟨hvalid.1.1.1.le, le_rfl⟩).2
  have hc : stateConstraint y = 1 := (normalizedMaxCurve_constraint hvalid.1.1.2.1).trans
    (fromProjectiveState_constraint (ne_of_gt (connection_entry_denom_pos hμ hu hw)))
  have hF : projectiveField (toProjectiveState y) 3 ≠ 0 := by
    intro heq
    have hr := hvalid.2.2.2
    rw [normalizedEventRate, projectiveGrowingWall_fderiv hA, toProjectiveState_fderiv_field hA hc] at hr
    change 0 < (1 + y 0) * projectiveField (toProjectiveState y) 3 at hr
    rw [heq, mul_zero] at hr
    exact lt_irrefl _ hr
  constructor
  · rw [htime.fderiv]
    change -(normalizedEventRate projectiveGrowingWall x 0 T)⁻¹ *
      fderiv ℝ projectiveGrowingWall y (normalizedFlowDifferential x 0 T (fderiv ℝ connectionInitialState p v)) = _
    rw [projectiveGrowingWall_fderiv hA]
  · rw [hstate.fderiv]
    exact projective_growing_event_differential hA hc hF (fderiv ℝ connectionInitialState p v)

theorem connectionReturn_growing_component {p : ConnectionParameters} (hμ : 4 ≤ p 0)
    (hu : 0 ≤ p 1 ∧ p 1 ≤ (1 / 10000) / p 0) (hw : 0 < p 2 ∧ p 2 ≤ 1 / 10000) :
    connectionReturnState p 3 = 1 ∧ ∀ v : ConnectionParameters, fderiv ℝ connectionReturnState p v 3 = 0 := by
  have H := connectionReturn_regular hμ hu hw
  have heq : (fun q => connectionReturnState q 3) =ᶠ[𝓝 p] (fun _ => (1 : ℝ)) := by
    filter_upwards [H.2.2.2.2.2] with q hq
    exact hq.1.1.2.2
  have hd := (hasFDerivAt_const (𝕜 := ℝ) (1 : ℝ) p).congr_of_eventuallyEq heq
  have hc := (hasFDerivAt_apply (𝕜 := ℝ) (3 : Fin 4) (connectionReturnState p)).comp p
    ((H.2.2.1.differentiableAt (by norm_num)).hasFDerivAt)
  refine ⟨heq.self_of_nhds, ?_⟩
  intro v
  have hlinear := hc.unique hd
  exact congrArg (fun L : ConnectionParameters →L[ℝ] ℝ => L v) hlinear

end BianchiIX
