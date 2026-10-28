import BianchiIX.Dynamics.RestartProjectionHeightBounds
import BianchiIX.Dynamics.RestartFastEntryControl

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

def restartFastProjectionHeight (h T θ ζ ρ : ℝ) : ℝ :=
  1 + normalizedMaxCurve (restartSectionChart h (restartRadialCurve θ ζ ρ)) 0 T 0

theorem eventually_restartSectionProjectionHeight_eq {h T : ℝ} {Z : RestartCenterState}
    (hrad : 0 < restartSectionRadicand h Z) (hT : 0 ≤ T)
    (hneg : normalizedMaxCurve (restartSectionChart h Z) 0 T 0 < 0) :
    (fun W => restartProjectionHeight (restartSectionRadialState h T W)) =ᶠ[𝓝 Z]
      (fun W => 1 + normalizedMaxCurve (restartSectionChart h W) 0 T 0) := by
  have hdom := normalizedMaxDomain_contains_Ici_of_constraint (restartSectionChart_constraint hrad.le) 0 hT
  have Hchart := (contDiffAt_restartSectionChart hrad 1).continuousAt
  have Hflow := (hasFDerivAt_normalizedMaxCurve_initial hdom).continuousAt.comp Hchart
  have Hcoord : ContinuousAt (fun W => normalizedMaxCurve (restartSectionChart h W) 0 T 0) Z :=
    (continuous_apply 0).continuousAt.comp Hflow
  have HR : ContinuousAt (restartSectionRadicand h) Z := by
    unfold restartSectionRadicand curvature
    fun_prop
  filter_upwards [HR.eventually (isOpen_Ioi.mem_nhds hrad),
    Hcoord.eventually (isOpen_Iio.mem_nhds hneg)] with W hW hN
  have HC := (normalizedMaxCurve_forward_of_constraint (restartSectionChart_constraint hW.le) hT).2.1
  exact restartProjectionHeight_of_constraint HC hN

theorem restartFastProjectionHeight_bounds {h T θ ζ ρ r R D : ℝ} {v : RestartRadialState}
    (hrad : 0 < restartSectionRadicand h (restartRadialCurve θ ζ ρ)) (hT : 0 ≤ T)
    (hneg : normalizedMaxCurve (restartSectionChart h (restartRadialCurve θ ζ ρ)) 0 T 0 < 0)
    (H : HasDerivAt (fun y => restartSectionRadialState h T (restartRadialCurve θ ζ y)) v ρ)
    (hr : 0 < r) (hp : ‖restartSectionRadialState h T (restartRadialCurve θ ζ ρ)‖ ≤ R)
    (hR : R ≤ 1 / 16)
    (ha : r / 2 ≤ (restartSectionRadialState h T (restartRadialCurve θ ζ ρ)).2 1)
    (hn : 0 ≤ (restartSectionRadialState h T (restartRadialCurve θ ζ ρ)).1 ∧
      (restartSectionRadialState h T (restartRadialCurve θ ζ ρ)).1 ≤
        (restartSectionRadialState h T (restartRadialCurve θ ζ ρ)).2 1 / 16)
    (hb : 0 ≤ (restartSectionRadialState h T (restartRadialCurve θ ζ ρ)).2 2 ∧
      (restartSectionRadialState h T (restartRadialCurve θ ζ ρ)).2 2 ≤
        (restartSectionRadialState h T (restartRadialCurve θ ζ ρ)).2 1 / 16)
    (hv : ‖v‖ ≤ D) :
    DifferentiableAt ℝ (restartFastProjectionHeight h T θ ζ) ρ ∧
      r ^ 2 / 16 ≤ restartFastProjectionHeight h T θ ζ ρ ∧
      restartFastProjectionHeight h T θ ζ ρ ≤ 10 * R ^ 2 ∧
      |deriv (restartFastProjectionHeight h T θ ζ) ρ| ≤ 32 * R * D := by
  obtain ⟨Hd, Hlo, Hhi⟩ := restartProjectionHeight_bounds hr hp hR ha hn hb
  have Hgerm := (eventually_restartSectionProjectionHeight_eq hrad hT hneg).comp_tendsto
    (hasDerivAt_restartRadialCurve θ ζ ρ).continuousAt
  change (fun y => restartProjectionHeight (restartSectionRadialState h T (restartRadialCurve θ ζ y))) =ᶠ[𝓝 ρ]
    restartFastProjectionHeight h T θ ζ at Hgerm
  have HD := restartProjectionHeight_derivative_bound H Hd.2 hp hv
  have Hactual := HD.1.hasDerivAt.congr_of_eventuallyEq Hgerm.symm
  rw [Hgerm.eq_of_nhds] at Hlo Hhi
  exact ⟨Hactual.differentiableAt, Hlo, Hhi, by rw [Hactual.deriv]; exact HD.2⟩

end BianchiIX
