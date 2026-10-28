import BianchiIX.Dynamics.SectionArrivalJacobian
import BianchiIX.Dynamics.AxisEvents

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

/-- Every actual wall hit from a transverse constraint chart has a nonsingular local arrival map. -/
theorem exists_transverse_axisWall_arrival (A : NormalizedSymmetry)
    {C : SectionCoordinates → NormalizedState} {y : SectionCoordinates} {t₀ t h : ℝ}
    (hC : ContDiffAt ℝ 1 C y) (hp : positiveWalls (C y))
    (hc : ∀ᶠ v in 𝓝 y, stateConstraint (C v) = 1)
    (hflux : normalizedSectionFlux (C y) (fun i => fderiv ℝ C y (Pi.single i 1)) ≠ 0)
    (ht : t ∈ normalizedMaxDomain (C y) t₀) (hh : 0 < h)
    (hlevel : A.map (normalizedMaxCurve (C y) t₀ t) 2 = h)
    (hneg : A.map (normalizedMaxCurve (C y) t₀ t) 0 < 0) :
    ∃ R : SectionCoordinates → SectionCoordinates, ContDiffAt ℝ 1 R y ∧
      (fderiv ℝ R y).det ≠ 0 ∧
      ∀ᶠ p : SectionCoordinates × ℝ in 𝓝 (y, t),
        A.map (normalizedMaxCurve (C p.1) t₀ p.2) 2 = h →
          R p.1 = axisWallCoordinates A (normalizedMaxCurve (C p.1) t₀ p.2) := by
  obtain ⟨τ, hτ, hcτ, hhit, huniq, hcMap⟩ :=
    exists_normalized_axisWall_event A ht hh hlevel hneg
  let F := fun v => normalizedMaxCurve (C v) t₀ (τ (C v))
  let R := fun v => axisWallCoordinates A (F v)
  have hF : ContDiffAt ℝ 1 F y := hcMap.comp y hC
  have hFy : F y = normalizedMaxCurve (C y) t₀ t := by simp only [F, hτ]
  have hpF : positiveWalls (F y) := by
    rw [hFy]
    exact ((maximalNormalizedSolution (C y) t₀).physical hp hc.self_of_nhds ht).1
  have hR : ContDiffAt ℝ 1 R y := (contDiffAt_axisWallCoordinates A hpF 1).comp y hF
  have hpos : ∀ᶠ v in 𝓝 y, positiveWalls (F v) :=
    hF.continuousAt.eventually (isOpen_positiveWalls.mem_nhds hpF)
  have hnegative : ∀ᶠ v in 𝓝 y, A.map (F v) 0 < 0 := by
    have H : ContinuousAt (fun v => A.map (F v) 0) y := by fun_prop
    exact H.eventually_lt continuousAt_const (by rw [hFy]; exact hneg)
  have hlocal : ∀ᶠ v in 𝓝 y, R v ∈ mainWallChartDomain h ∧ axisWallChart A h (R v) = F v := by
    filter_upwards [hc, hC.continuousAt.eventually hhit, hpos, hnegative] with v hcv htv hpv hnv
    exact axisWallChart_coordinates A hpv ((normalizedMaxCurve_constraint htv.1).trans hcv) hnv htv.2
  have hdet : (fderiv ℝ R y).det ≠ 0 :=
    normalized_chart_arrival_det_ne_zero (hC.differentiableAt (by norm_num))
      ((contDiffAt_axisWallChart A hlocal.self_of_nhds.1 1).differentiableAt (by norm_num))
      (hR.differentiableAt (by norm_num)) (hcτ.differentiableAt (by norm_num)) hp hc
      (by rw [hτ]; exact ht) hflux (hlocal.mono fun _ hv => hv.2)
  refine ⟨R, hR, hdet, ?_⟩
  have hpair : Tendsto (fun p : SectionCoordinates × ℝ => (C p.1, p.2))
      (𝓝 (y, t)) (𝓝 (C y, t)) :=
    (hC.continuousAt.comp continuousAt_fst).prodMk continuousAt_snd
  filter_upwards [hpair.eventually huniq] with p hp hlevel'
  have htime : τ (C p.1) = p.2 := hp.2.mp hlevel'
  simp only [R, F, htime]

end BianchiIX
