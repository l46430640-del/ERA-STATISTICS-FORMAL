import BianchiIX.Dynamics.EntranceReturn
import BianchiIX.Dynamics.ProjectiveFlowVariation

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

/-- The moving endpoint removes exactly the active-wall component of the fixed-time variation. -/
theorem entranceReturn_differential {y : ProjectiveState}
    (hk : 7 / 4 ≤ coreRadius (y 0) (y 2)) (hm : 1 ≤ y 0)
    (hu : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000) (hv : 0 < y 2 ∧ y 2 < 1)
    (hw : 0 ≤ y 3 ∧ y 3 ≤ 1 / 10000) (v : ProjectiveState) :
    let x := fromProjectiveState y
    let T := entranceReturnTime y
    let ξ := projectiveFlowDifferential y 0 T v
    fderiv ℝ entranceReturnTime y v = -(normalizedEventRate projectiveActiveWall x 0 T)⁻¹ * ξ 2 ∧
      fderiv ℝ entranceReturnState y v =
        ξ - (ξ 2 / projectiveField (entranceReturnState y) 2) • projectiveField (entranceReturnState y) := by
  intro x T ξ
  have H := entranceReturn_regular hk hm hu hv hw
  have hvalid := H.1
  have htime := H.2.2.2.1
  have hstate := H.2.2.2.2.1
  have hT : T ∈ Icc 0 T := ⟨hvalid.1.1.1.le, le_rfl⟩
  have hA : 1 + normalizedMaxCurve x 0 T 0 ≠ 0 := (hvalid.2.1 T hT).2.ne'
  have hc : stateConstraint (normalizedMaxCurve x 0 T) = 1 :=
    (normalizedMaxCurve_constraint hvalid.1.1.2.1).trans
      (fromProjectiveState_constraint (entrance_initial_denom_pos hk hm hu hv hw).ne')
  have hF : projectiveField (entranceReturnState y) 2 ≠ 0 := by
    intro heq
    have hr := hvalid.2.2.2 T hT
    rw [normalizedEventRate, projectiveActiveWall_fderiv_field hA hc] at hr
    change 0 < (1 + normalizedMaxCurve x 0 T 0) * projectiveField (entranceReturnState y) 2 at hr
    rw [heq, mul_zero] at hr
    exact lt_irrefl _ hr
  constructor
  · rw [htime.fderiv]
    change -(normalizedEventRate projectiveActiveWall x 0 T)⁻¹ *
      fderiv ℝ projectiveActiveWall (normalizedMaxCurve x 0 T)
        (normalizedFlowDifferential x 0 T (fderiv ℝ fromProjectiveState y v)) = _
    rw [projectiveActiveWall_fderiv hA]
    rfl
  · rw [hstate.fderiv]
    exact projective_event_differential hA hc hF (fderiv ℝ fromProjectiveState y v)

theorem entranceReturn_active_component {y : ProjectiveState}
    (hk : 7 / 4 ≤ coreRadius (y 0) (y 2)) (hm : 1 ≤ y 0)
    (hu : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000) (hv : 0 < y 2 ∧ y 2 < 1)
    (hw : 0 ≤ y 3 ∧ y 3 ≤ 1 / 10000) :
    entranceReturnState y 2 = 1 ∧ ∀ v : ProjectiveState, fderiv ℝ entranceReturnState y v 2 = 0 := by
  have H := entranceReturn_regular hk hm hu hv hw
  have heq : (fun z => entranceReturnState z 2) =ᶠ[𝓝 y] (fun _ => (1 : ℝ)) := by
    filter_upwards [H.2.2.2.2.2] with z hz
    exact hz.1.1.2.2
  have hd := (hasFDerivAt_const (𝕜 := ℝ) (1 : ℝ) y).congr_of_eventuallyEq heq
  have hc := (hasFDerivAt_apply (𝕜 := ℝ) (2 : Fin 4) (entranceReturnState y)).comp y
    ((H.2.2.1.differentiableAt (by norm_num)).hasFDerivAt)
  refine ⟨heq.self_of_nhds, ?_⟩
  intro v
  exact congrArg (fun L : ProjectiveState →L[ℝ] ℝ => L v) (hc.unique hd)

end BianchiIX
