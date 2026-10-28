import BianchiIX.Dynamics.RestartCenterVariation

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

def restartSectionStrongWall (h t : ℝ) (Z : RestartCenterState) : ℝ :=
  normalizedMaxCurve (restartSectionChart h Z) 0 t 2

def restartSectionStrongLog (h t : ℝ) (Z : RestartCenterState) : ℝ :=
  Real.log (restartSectionStrongWall h t Z)

theorem contDiffAt_restartSectionChart {h : ℝ} {Z : RestartCenterState}
    (hZ : 0 < restartSectionRadicand h Z) (k : WithTop ℕ∞) :
    ContDiffAt ℝ k (restartSectionChart h) Z := by
  have hr : ContDiff ℝ k (restartSectionRadicand h) := by
    unfold restartSectionRadicand curvature
    fun_prop
  rw [contDiffAt_pi]
  intro i
  fin_cases i
  · exact (hr.contDiffAt.sqrt hZ.ne').neg
  · exact contDiffAt_apply ℝ ℝ (0 : Fin 3) Z
  · exact contDiffAt_const
  · exact contDiffAt_apply ℝ ℝ (1 : Fin 3) Z
  · exact contDiffAt_apply ℝ ℝ (2 : Fin 3) Z

theorem contDiffAt_restartSectionStrongWall {h t : ℝ} {Z : RestartCenterState}
    (hZ : 0 < restartSectionRadicand h Z)
    (ht : t ∈ normalizedMaxDomain (restartSectionChart h Z) 0) :
    ContDiffAt ℝ 2 (restartSectionStrongWall h t) Z := by
  have H : ContDiffAt ℝ 2
      (fun W => normalizedMaxCurve (restartSectionChart h W) 0 t) Z :=
    (contDiffAt_normalizedMaxCurve_two ht).comp Z
      (g := fun z : NormalizedState × ℝ => normalizedMaxCurve z.1 0 z.2)
      ((contDiffAt_restartSectionChart hZ 2).prodMk (contDiffAt_const (c := t)))
  exact (contDiffAt_apply ℝ ℝ (2 : Fin 5) _).comp Z H

theorem restartSectionStrongWall_pos {h t : ℝ} {Z : RestartCenterState}
    (hh : 0 < h) (hZ : 0 ≤ restartSectionRadicand h Z) (ht : 0 ≤ t) :
    0 < restartSectionStrongWall h t Z := by
  have H := normalizedMaxCurve_wall_sign (restartSectionChart_constraint hZ) ht (0 : Fin 3)
  change (restartSectionStrongWall h t Z = 0 ↔ h = 0) ∧
    (0 ≤ restartSectionStrongWall h t Z ↔ 0 ≤ h) at H
  have hne : restartSectionStrongWall h t Z ≠ 0 := fun he => hh.ne' (H.1.mp he)
  exact lt_of_le_of_ne (H.2.mpr hh.le) hne.symm

theorem restartSectionStrongWall_zero (h t : ℝ) :
    restartSectionStrongWall h t 0 = restartReferenceCurve h t 2 := by
  rw [restartSectionStrongWall, restartSectionChart_zero]
  rfl

theorem restartSectionStrongLog_eq {h : ℝ} (hh : 0 < h) (t : ℝ) (Z : RestartCenterState) :
    restartSectionStrongLog h t Z = restartSectionMixedFlow h t Z 0 := by
  rw [restartSectionMixedFlow_physical hh]
  rfl

theorem hasFDerivAt_restartSectionStrongLog {h t : ℝ} {Z : RestartCenterState}
    (hh : 0 < h) (HD : DifferentiableAt ℝ (restartSectionMixedFlow h t) Z) :
    HasFDerivAt (restartSectionStrongLog h t)
      ((ContinuousLinearMap.proj (0 : Fin 4)).comp (fderiv ℝ (restartSectionMixedFlow h t) Z)) Z := by
  have H := (hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 4) (restartSectionMixedFlow h t Z)).comp Z HD.hasFDerivAt
  convert! H using 1
  ext W
  exact restartSectionStrongLog_eq hh t W

theorem restartSectionStrongLog_fderiv_norm_le {h t : ℝ} {Z : RestartCenterState}
    (hh : 0 < h) (HD : DifferentiableAt ℝ (restartSectionMixedFlow h t) Z) :
    ‖fderiv ℝ (restartSectionStrongLog h t) Z‖ ≤ ‖fderiv ℝ (restartSectionMixedFlow h t) Z‖ := by
  rw [(hasFDerivAt_restartSectionStrongLog hh HD).fderiv]
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro v
  exact (norm_le_pi_norm (fderiv ℝ (restartSectionMixedFlow h t) Z v) 0).trans
    ((fderiv ℝ (restartSectionMixedFlow h t) Z).le_opNorm v)

/-- Exponentiating the actual logarithmic observable recovers its ordinary wall derivative. -/
theorem hasFDerivAt_restartSectionStrongWall {h t : ℝ} {Z : RestartCenterState}
    (hh : 0 < h) (hZ : 0 < restartSectionRadicand h Z) (ht : 0 ≤ t)
    (HD : DifferentiableAt ℝ (restartSectionMixedFlow h t) Z) :
    HasFDerivAt (restartSectionStrongWall h t)
      (restartSectionStrongWall h t Z • fderiv ℝ (restartSectionStrongLog h t) Z) Z := by
  have hdom := normalizedMaxDomain_contains_Ici_of_constraint (restartSectionChart_constraint hZ.le) 0 ht
  have hn := restartSectionStrongWall_pos hh hZ.le ht
  have Hlog := (hasFDerivAt_restartSectionStrongLog hh HD).differentiableAt.hasFDerivAt
  have HE := Hlog.exp
  have heq : (fun W => Real.exp (restartSectionStrongLog h t W)) =ᶠ[𝓝 Z] restartSectionStrongWall h t := by
    filter_upwards [(contDiffAt_restartSectionStrongWall hZ hdom).continuousAt.eventually
      (isOpen_Ioi.mem_nhds hn)] with W hW
    exact Real.exp_log hW
  have H := HE.congr_of_eventuallyEq heq.symm
  simpa only [restartSectionStrongLog, Real.exp_log hn] using H

theorem restartSectionStrongWall_fderiv_norm {h t : ℝ} {Z : RestartCenterState}
    (hh : 0 < h) (hZ : 0 < restartSectionRadicand h Z) (ht : 0 ≤ t)
    (HD : DifferentiableAt ℝ (restartSectionMixedFlow h t) Z) :
    ‖fderiv ℝ (restartSectionStrongWall h t) Z‖ =
      restartSectionStrongWall h t Z * ‖fderiv ℝ (restartSectionStrongLog h t) Z‖ := by
  rw [(hasFDerivAt_restartSectionStrongWall hh hZ ht HD).fderiv, norm_smul, Real.norm_eq_abs,
    abs_of_pos (restartSectionStrongWall_pos hh hZ.le ht)]

end BianchiIX
