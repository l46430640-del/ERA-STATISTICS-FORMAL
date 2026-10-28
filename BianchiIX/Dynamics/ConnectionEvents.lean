import BianchiIX.Dynamics.Events
import BianchiIX.Dynamics.ConnectionFirstReturn

noncomputable section

namespace BianchiIX

open Set

def projectiveGrowingWall (x : NormalizedState) : ℝ := toProjectiveState x 3

theorem contDiffAt_projectiveGrowingWall (n : WithTop ℕ∞) {x : NormalizedState}
    (hA : 1 + x 0 ≠ 0) : ContDiffAt ℝ n projectiveGrowingWall x :=
  contDiffAt_pi.mp (contDiffAt_toProjectiveState n hA) 3

theorem projectiveGrowingWall_fderiv {x : NormalizedState}
    (hA : 1 + x 0 ≠ 0) (v : NormalizedState) :
    fderiv ℝ projectiveGrowingWall x v = (fderiv ℝ toProjectiveState x v) 3 := by
  have hd := (hasFDerivAt_apply (𝕜 := ℝ) (3 : Fin 4) (toProjectiveState x)).comp x
    ((contDiffAt_toProjectiveState 1 hA).differentiableAt (by norm_num)).hasFDerivAt
  rw [show fderiv ℝ projectiveGrowingWall x = _ from hd.fderiv]
  rfl

theorem projectiveGrowingWall_fderiv_field {x : NormalizedState}
    (hA : 1 + x 0 ≠ 0) (hc : stateConstraint x = 1) :
    fderiv ℝ projectiveGrowingWall x (normalizedField x) =
      (1 + x 0) * (connectionClockRate (toProjectiveState x) * toProjectiveState x 3) := by
  rw [projectiveGrowingWall_fderiv hA, toProjectiveState_fderiv_field hA hc]
  rfl

theorem normalized_connection_event_rate_pos {x : NormalizedState} {t₀ s t μ : ℝ}
    (hc : stateConstraint x = 1) (hμ : 4 ≤ μ) (hs : t₀ ≤ s) (hst : s ≤ t)
    (hAs : 0 < 1 + normalizedMaxCurve x t₀ s 0) (hAt : 0 < 1 + normalizedMaxCurve x t₀ t 0)
    (hy : connectionRegion μ (toProjectiveState (normalizedMaxCurve x t₀ t)))
    (hw : 0 < projectiveGrowingWall (normalizedMaxCurve x t₀ s)) :
    0 < normalizedEventRate projectiveGrowingWall x t₀ t := by
  have hd := normalizedMaxDomain_contains_Ici_of_constraint hc t₀ (hs.trans hst)
  have hds := normalizedMaxDomain_contains_Ici_of_constraint hc t₀ hs
  have hwpos := normalized_projective_wall_pos hds hd hAs hAt 2 hw
  have hD : 0 < connectionClockRate (toProjectiveState (normalizedMaxCurve x t₀ t)) := by
    have H := (connection_speed_bounds hμ hy.1 hy.2.1 hy.2.2.1 hy.2.2.2).1
    change μ / 2 ≤ connectionClockRate (toProjectiveState (normalizedMaxCurve x t₀ t)) at H
    linarith only [H, hμ]
  rw [normalizedEventRate, projectiveGrowingWall_fderiv_field (ne_of_gt hAt)
    ((normalizedMaxCurve_constraint hd).trans hc)]
  exact mul_pos hAt (mul_pos hD hwpos)

/-- The event correction removes the growing-wall component of the fixed-time variation. -/
theorem projective_growing_event_differential {x : NormalizedState} {t₀ t : ℝ}
    (hA : 1 + normalizedMaxCurve x t₀ t 0 ≠ 0)
    (hc : stateConstraint (normalizedMaxCurve x t₀ t) = 1)
    (hw : projectiveField (toProjectiveState (normalizedMaxCurve x t₀ t)) 3 ≠ 0)
    (v : NormalizedState) :
    let y := normalizedMaxCurve x t₀ t
    let ξ := fderiv ℝ toProjectiveState y (normalizedFlowDifferential x t₀ t v)
    fderiv ℝ toProjectiveState y (normalizedEventDifferential projectiveGrowingWall x t₀ t v) =
      ξ - (ξ 3 / projectiveField (toProjectiveState y) 3) • projectiveField (toProjectiveState y) := by
  dsimp only
  change fderiv ℝ toProjectiveState (normalizedMaxCurve x t₀ t)
    (normalizedFlowDifferential x t₀ t v +
      (-(fderiv ℝ projectiveGrowingWall (normalizedMaxCurve x t₀ t)
        (normalizedField (normalizedMaxCurve x t₀ t)))⁻¹ *
          fderiv ℝ projectiveGrowingWall (normalizedMaxCurve x t₀ t)
            (normalizedFlowDifferential x t₀ t v)) • normalizedField (normalizedMaxCurve x t₀ t)) = _
  rw [map_add, map_smul, projectiveGrowingWall_fderiv hA (normalizedField _),
    toProjectiveState_fderiv_field hA hc, projectiveGrowingWall_fderiv hA]
  ext i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  field_simp
  ring

end BianchiIX
