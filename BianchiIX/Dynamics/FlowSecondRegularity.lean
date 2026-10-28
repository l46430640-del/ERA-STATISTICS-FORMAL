import BianchiIX.Dynamics.TangentRegularity
import BianchiIX.Dynamics.FlowSmoothRegularity

noncomputable section

namespace BianchiIX

open Set Filter Metric
open scoped Topology

/-- The second-order statement is a specialization of joint smoothness. -/
theorem contDiffAt_normalizedMaxCurve_two {x : NormalizedState} {t₀ t : ℝ}
    (ht : t ∈ normalizedMaxDomain x t₀) :
    ContDiffAt ℝ 2 (fun z : NormalizedState × ℝ => normalizedMaxCurve z.1 t₀ z.2) (x, t) :=
  (contDiffAt_normalizedMaxCurve_smooth ht).of_le (by decide)

theorem contDiffOn_normalizedMaxCurve_two (t₀ : ℝ) :
    ContDiffOn ℝ 2 (fun z : NormalizedState × ℝ => normalizedMaxCurve z.1 t₀ z.2)
      (normalizedFlowDomain t₀) :=
  fun _ hz => (contDiffAt_normalizedMaxCurve_two hz).contDiffWithinAt

theorem contDiffOn_normalizedFlowDifferential_one (t₀ : ℝ) :
    ContDiffOn ℝ 1 (fun z : NormalizedState × ℝ => normalizedFlowDifferential z.1 t₀ z.2)
      (normalizedFlowDomain t₀) := by
  have hc := (contDiffOn_normalizedMaxCurve_two t₀).fderiv_of_isOpen
    (isOpen_normalizedFlowDomain t₀) (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)
  exact (hc.clm_comp (contDiffOn_const (c := ContinuousLinearMap.inl ℝ NormalizedState ℝ))).congr
    (fun z hz => (normalizedMaxCurve_fderiv_initial hz).symm)

end BianchiIX
