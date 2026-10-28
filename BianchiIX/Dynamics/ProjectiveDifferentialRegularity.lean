import BianchiIX.Dynamics.ProjectiveFlowSecondRegularity

noncomputable section

namespace BianchiIX

open Set

theorem contDiffAt_projectiveFlowDifferential_one {y : ProjectiveState} {t₀ t : ℝ}
    (hD : 0 < projectiveStateDenom y) (ht : t ∈ normalizedMaxDomain (fromProjectiveState y) t₀)
    (hA : 0 < 1 + normalizedMaxCurve (fromProjectiveState y) t₀ t 0) :
    ContDiffAt ℝ 1 (fun z : ProjectiveState × ℝ => projectiveFlowDifferential z.1 t₀ z.2) (y, t) := by
  have hparam : ContDiffAt ℝ 1 (fun z : ProjectiveState × ℝ => (fromProjectiveState z.1, z.2)) (y, t) :=
    ((contDiffAt_fromProjectiveState 1 hD.ne').comp (y, t) contDiffAt_fst).prodMk contDiffAt_snd
  have hN : ContDiffAt ℝ 1
      (fun z : ProjectiveState × ℝ => normalizedMaxCurve (fromProjectiveState z.1) t₀ z.2) (y, t) := by
    have H := ((contDiffAt_normalizedMaxCurve_two ht).of_le
      (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).comp (y, t) hparam
    simpa only [Function.comp_def] using H
  have hJ := ((contDiffOn_normalizedFlowDifferential_one t₀).contDiffAt
    ((isOpen_normalizedFlowDomain t₀).mem_nhds ht)).comp (y, t) hparam
  have hto := ((contDiffAt_toProjectiveState 2 hA.ne').fderiv_right
    (m := 1) (by norm_num)).comp (y, t) hN
  have hfrom := ((contDiffAt_fromProjectiveState 2 hD.ne').fderiv_right
    (m := 1) (by norm_num)).comp (y, t) contDiffAt_fst
  exact hto.clm_comp (hJ.clm_comp hfrom)

end BianchiIX
