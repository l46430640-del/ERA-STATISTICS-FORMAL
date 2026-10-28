import BianchiIX.Dynamics.RestartRadiusDifferential
import BianchiIX.Analysis.PartialDerivativeTime

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

def restartSectionRadiusRegular (h : ℝ) (p : RestartCenterState × ℝ) : Prop :=
  0 < restartSectionRadicand h p.1 ∧
    p.2 ∈ normalizedMaxDomain (restartSectionChart h p.1) 0 ∧
    normalizedMaxCurve (restartSectionChart h p.1) 0 p.2 0 < 0 ∧
    restartSectionStrongWall h p.2 p.1 ^ 2 < 1 ∧ 0 < restartSectionQuadratic h p.2 p.1

theorem contDiffAt_restartSectionRadialState_joint {h : ℝ} {p : RestartCenterState × ℝ}
    (hr : 0 < restartSectionRadicand h p.1)
    (ht : p.2 ∈ normalizedMaxDomain (restartSectionChart h p.1) 0) :
    ContDiffAt ℝ 2 (fun q : RestartCenterState × ℝ => restartSectionRadialState h q.2 q.1) p := by
  have HX : ContDiffAt ℝ 2
      (fun q : RestartCenterState × ℝ => normalizedMaxCurve (restartSectionChart h q.1) 0 q.2) p :=
    (contDiffAt_normalizedMaxCurve_two ht).comp p
      (g := fun z : NormalizedState × ℝ => normalizedMaxCurve z.1 0 z.2)
      (((contDiffAt_restartSectionChart hr 2).comp p contDiffAt_fst).prodMk contDiffAt_snd)
  exact ((contDiffAt_apply ℝ ℝ (2 : Fin 5) _).comp p HX).prodMk
    (restartCenterProjection.contDiff.contDiffAt.comp p HX)

theorem contDiffAt_restartSectionRadius_joint {h : ℝ} {p : RestartCenterState × ℝ}
    (hp : restartSectionRadiusRegular h p) :
    ContDiffAt ℝ 2 (fun q : RestartCenterState × ℝ => restartSectionRadius h q.2 q.1) p := by
  have Hstate := contDiffAt_restartSectionRadialState_joint hp.1 hp.2.1
  have HQ := (contDiffAt_restartRadialQuadratic (p := restartSectionRadialState h p.2 p.1) hp.2.2.2.1 2).comp p Hstate
  exact HQ.sqrt hp.2.2.2.2.ne'

theorem restartSectionRadiusRegular_eventually {h : ℝ} {p : RestartCenterState × ℝ}
    (hp : restartSectionRadiusRegular h p) : ∀ᶠ q in 𝓝 p, restartSectionRadiusRegular h q := by
  have Hchart := (contDiffAt_restartSectionChart hp.1 2).comp p contDiffAt_fst
  have HX : ContDiffAt ℝ 2
      (fun q : RestartCenterState × ℝ => normalizedMaxCurve (restartSectionChart h q.1) 0 q.2) p :=
    (contDiffAt_normalizedMaxCurve_two hp.2.1).comp p
      (g := fun z : NormalizedState × ℝ => normalizedMaxCurve z.1 0 z.2) (Hchart.prodMk contDiffAt_snd)
  have Hr : ContinuousAt (fun q : RestartCenterState × ℝ => restartSectionRadicand h q.1) p := by
    unfold restartSectionRadicand curvature
    fun_prop
  have Hneg := (continuous_apply (0 : Fin 5)).continuousAt.comp HX.continuousAt
  have Hn := ((continuous_apply (2 : Fin 5)).continuousAt.comp HX.continuousAt).pow 2
  have HQ := (contDiffAt_restartRadialQuadratic (p := restartSectionRadialState h p.2 p.1) hp.2.2.2.1 2).comp p
    (contDiffAt_restartSectionRadialState_joint hp.1 hp.2.1)
  filter_upwards [Hr.eventually (isOpen_Ioi.mem_nhds hp.1),
    (Hchart.continuousAt.prodMk continuousAt_snd).eventually ((isOpen_normalizedFlowDomain 0).mem_nhds hp.2.1),
    Hneg.eventually (isOpen_Iio.mem_nhds hp.2.2.1), Hn.eventually (isOpen_Iio.mem_nhds hp.2.2.2.1),
    HQ.continuousAt.eventually (isOpen_Ioi.mem_nhds hp.2.2.2.2)] with q hqr hqt hqp hqn hqJ
  exact ⟨hqr, hqt, hqp, hqn, hqJ⟩

theorem hasDerivAt_restartSectionRadius_time {h t : ℝ} {Z : RestartCenterState}
    (hp : restartSectionRadiusRegular h (Z, t)) :
    HasDerivAt (fun s => restartSectionRadius h s Z) (restartSectionRadiusRate h t Z) t := by
  have HJ := hasDerivAt_restartQuadratic_drift (hasDerivAt_normalizedMaxCurve hp.2.1)
    ((normalizedMaxCurve_constraint hp.2.1).trans (restartSectionChart_constraint hp.1.le))
    hp.2.2.1 hp.2.2.2.1
  exact hasDerivAt_restartSectionRadius HJ hp.2.2.2.2

theorem restartSectionRadius_local_time {h : ℝ} {p : RestartCenterState × ℝ}
    (hp : restartSectionRadiusRegular h p) :
    (fun q => fderiv ℝ (fun z : RestartCenterState × ℝ => restartSectionRadius h z.2 z.1) q (0, 1)) =ᶠ[𝓝 p]
      (fun q => restartSectionRadiusRate h q.2 q.1) := by
  filter_upwards [restartSectionRadiusRegular_eventually hp] with q hq
  have H := ((contDiffAt_restartSectionRadius_joint hq).differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt q.2
    ((hasDerivAt_const q.2 q.1).prodMk (hasDerivAt_id q.2))
  exact H.unique (hasDerivAt_restartSectionRadius_time hq)

/-- The ordinary initial derivative differentiates in time to the ordinary derivative of the rate. -/
theorem hasDerivAt_restartSectionRadius_variation {h t : ℝ} {Z : RestartCenterState}
    (hp : restartSectionRadiusRegular h (Z, t)) (v : RestartCenterState) :
    HasDerivAt (fun s => fderiv ℝ (restartSectionRadius h s) Z v)
      (fderiv ℝ (restartSectionRadiusRate h t) Z v) t :=
  hasDerivAt_parameter_fderiv_of_local_time (contDiffAt_restartSectionRadius_joint hp)
    (restartSectionRadius_local_time hp) v

end BianchiIX
