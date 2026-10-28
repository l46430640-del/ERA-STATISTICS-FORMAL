import BianchiIX.Dynamics.OrbitSaturation
import BianchiIX.Dynamics.AxisEvents
import BianchiIX.Dynamics.FlowInjectivity

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

def axisWallFlowDomain (A : NormalizedSymmetry) (h : ℝ) : Set (SectionCoordinates × ℝ) :=
  {p | p.1 ∈ mainWallChartDomain h ∧ p.2 ∈ normalizedMaxDomain (axisWallChart A h p.1) 0}

def axisWallFlowMap (A : NormalizedSymmetry) (h : ℝ) (p : SectionCoordinates × ℝ) : NormalizedState :=
  normalizedMaxCurve (axisWallChart A h p.1) 0 p.2

theorem isOpen_axisWallFlowDomain (A : NormalizedSymmetry) (h : ℝ) : IsOpen (axisWallFlowDomain A h) := by
  apply isOpen_iff_mem_nhds.mpr
  intro p hp
  have hpair : ContinuousAt (fun q : SectionCoordinates × ℝ => (axisWallChart A h q.1, q.2)) p :=
    ((contDiffAt_axisWallChart A hp.1 1).continuousAt.comp continuousAt_fst).prodMk continuousAt_snd
  exact (continuousAt_fst.eventually ((isOpen_mainWallChartDomain h).mem_nhds hp.1)).and
    (hpair.eventually ((isOpen_normalizedFlowDomain 0).mem_nhds hp.2))

theorem contDiffAt_axisWallFlowMap (A : NormalizedSymmetry) {h : ℝ} {p : SectionCoordinates × ℝ}
    (hp : p ∈ axisWallFlowDomain A h) : ContDiffAt ℝ 1 (axisWallFlowMap A h) p := by
  have H := normalizedMaxCurve_regular (x := axisWallChart A h p.1) (t₀ := 0) (t := p.2) hp.2
  exact H.2.comp p
    (((contDiffAt_axisWallChart A hp.1 1).comp p contDiffAt_fst).prodMk contDiffAt_snd)

/-- A reverse wall event recovers elapsed time and makes the orbit parametrization locally injective. -/
theorem exists_axisWallFlowMap_injOn (A : NormalizedSymmetry) {h : ℝ} (hh : 0 < h)
    {p : SectionCoordinates × ℝ} (hp : p ∈ axisWallFlowDomain A h) :
    ∃ V : Set (SectionCoordinates × ℝ), IsOpen V ∧ p ∈ V ∧ V ⊆ axisWallFlowDomain A h ∧
      InjOn (axisWallFlowMap A h) V := by
  have hinv := normalizedMaxCurve_inverse hp.2
  have hlevel : A.map (normalizedMaxCurve (axisWallFlowMap A h p) 0 (-p.2)) 2 = h := by
    rw [show normalizedMaxCurve (axisWallFlowMap A h p) 0 (-p.2) = axisWallChart A h p.1 from hinv.2,
      axisWallChart, ContinuousLinearEquiv.apply_symm_apply]
    rfl
  have hneg : A.map (normalizedMaxCurve (axisWallFlowMap A h p) 0 (-p.2)) 0 < 0 := by
    rw [show normalizedMaxCurve (axisWallFlowMap A h p) 0 (-p.2) = axisWallChart A h p.1 from hinv.2,
      axisWallChart, ContinuousLinearEquiv.apply_symm_apply]
    exact mainWallChart_negative hp.1
  obtain ⟨τ, _, _, _, huniq, _⟩ := exists_normalized_axisWall_event A hinv.1 hh hlevel hneg
  have hpair : ContinuousAt (fun q : SectionCoordinates × ℝ => (axisWallFlowMap A h q, -q.2)) p :=
    (contDiffAt_axisWallFlowMap A hp).continuousAt.prodMk continuousAt_snd.neg
  have hrecover : ∀ᶠ q : SectionCoordinates × ℝ in 𝓝 p,
      q ∈ axisWallFlowDomain A h ∧ τ (axisWallFlowMap A h q) = -q.2 := by
    filter_upwards [(isOpen_axisWallFlowDomain A h).mem_nhds hp, hpair.eventually huniq] with q hq he
    refine ⟨hq, he.2.mp ?_⟩
    rw [show normalizedMaxCurve (axisWallFlowMap A h q) 0 (-q.2) = axisWallChart A h q.1 from
      (normalizedMaxCurve_inverse hq.2).2, axisWallChart, ContinuousLinearEquiv.apply_symm_apply]
    rfl
  obtain ⟨V, hV, hVo, hpV⟩ := mem_nhds_iff.mp hrecover
  refine ⟨V, hVo, hpV, fun _ hq => (hV hq).1, ?_⟩
  intro q hq r hr heq
  have htime : q.2 = r.2 := by
    have H := congrArg τ heq
    rw [(hV hq).2, (hV hr).2] at H
    exact neg_injective H
  apply Prod.ext _ htime
  apply axisWallChart_injective A h
  apply normalizedMaxCurve_injOn 0 q.2 (hV hq).1.2
    (by rw [htime]; exact (hV hr).1.2)
  simpa only [axisWallFlowMap, htime] using heq

end BianchiIX
