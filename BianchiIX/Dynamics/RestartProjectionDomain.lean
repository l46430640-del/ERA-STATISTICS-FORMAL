import BianchiIX.Dynamics.RestartProjectionPhase
import BianchiIX.Dynamics.RestartRadialVariation

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

theorem curvature_lower_of_active_dominance {n a b : ℝ} (ha : 0 < a)
    (hn : 0 ≤ n ∧ n ≤ a / 16) (hb : 0 ≤ b ∧ b ≤ a / 16) :
    3 / 4 * a ^ 2 ≤ curvature n a b := by
  have Hnb := mul_le_mul hn.2 hb.2 hb.1 (by positivity : 0 ≤ a / 16)
  have Hgap : 7 * a / 8 ≤ a - n - b := by linarith only [hn.2, hb.2]
  have Hsq := mul_self_le_mul_self (by positivity : 0 ≤ 7 * a / 8) Hgap
  unfold curvature
  nlinarith only [Hnb, Hsq]

theorem normalized_projective_height_pos_of_active_dominance {x : NormalizedState}
    (hc : stateConstraint x = 1) (ha : 0 < x 3)
    (hn : 0 ≤ x 2 ∧ x 2 ≤ x 3 / 16) (hb : 0 ≤ x 4 ∧ x 4 ≤ x 3 / 16) :
    0 < 1 + x 0 := by
  have H := curvature_lower_of_active_dominance ha hn hb
  have Hpos := sq_pos_of_pos ha
  dsimp only [stateConstraint, constraint, shearSq] at hc
  nlinarith only [H, Hpos, hc, sq_nonneg (x 1), sq_nonneg (x 0 + 1)]

/-- The phase identity holds in an open initial-data neighborhood, so it transfers ordinary derivatives. -/
theorem eventually_restartSectionProjectionPhase_eq_core {h T : ℝ} {Z : RestartCenterState}
    (hrad : 0 < restartSectionRadicand h Z) (hT : 0 ≤ T)
    (hneg : normalizedMaxCurve (restartSectionChart h Z) 0 T 0 < 0)
    (hheight : 0 < 1 + normalizedMaxCurve (restartSectionChart h Z) 0 T 0) :
    (fun W => restartProjectionPhase (restartSectionRadialState h T W)) =ᶠ[𝓝 Z]
      (fun W => let x := normalizedMaxCurve (restartSectionChart h W) 0 T
        2 / coreRadius (toProjectiveState x 0) (toProjectiveState x 2)) := by
  have hdom := normalizedMaxDomain_contains_Ici_of_constraint (restartSectionChart_constraint hrad.le) 0 hT
  have Hchart := (contDiffAt_restartSectionChart hrad 1).continuousAt
  have Hflow := (hasFDerivAt_normalizedMaxCurve_initial hdom).continuousAt.comp Hchart
  have Hcoord : ContinuousAt (fun W => normalizedMaxCurve (restartSectionChart h W) 0 T 0) Z :=
    (continuous_apply 0).continuousAt.comp Hflow
  have HR : ContinuousAt (restartSectionRadicand h) Z := by
    unfold restartSectionRadicand curvature
    fun_prop
  have HnearR := HR.eventually (isOpen_Ioi.mem_nhds hrad)
  have HnearN := Hcoord.eventually (isOpen_Iio.mem_nhds hneg)
  have HnearA := (continuousAt_const.add Hcoord).eventually (isOpen_Ioi.mem_nhds hheight)
  filter_upwards [HnearR, HnearN, HnearA] with W hW hN hA
  have HC := (normalizedMaxCurve_forward_of_constraint (restartSectionChart_constraint hW.le) hT).2.1
  exact restartProjectionPhase_eq_core HC hN hA

end BianchiIX
