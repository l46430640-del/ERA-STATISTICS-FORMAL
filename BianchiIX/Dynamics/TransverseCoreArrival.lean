import BianchiIX.Dynamics.SectionArrivalJacobian
import BianchiIX.Dynamics.ReferenceSectionMap
import BianchiIX.Dynamics.CoreSectionPhysical

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

def normalizedCoreCoordinates (x : NormalizedState) : SectionCoordinates :=
  coreSectionCoordinates (toProjectiveState x)

theorem coreSectionEmbedding_coordinates {z : ProjectiveState} (hz : z 2 = 1) :
    coreSectionEmbedding (coreSectionCoordinates z) = z := by
  ext i
  fin_cases i <;> simp [coreSectionEmbedding, coreSectionCoordinates, hz]

theorem coreSectionChart_reconstruct {x : NormalizedState}
    (hc : stateConstraint x = 1) (hv : projectiveActiveWall x = 1) :
    coreSectionChart (normalizedCoreCoordinates x) = x := by
  rw [coreSectionChart, normalizedCoreCoordinates, coreSectionEmbedding_coordinates hv]
  exact fromProjectiveState_toProjectiveState (unit_active_wall_clock_ne_zero hv) hc

theorem contDiffAt_normalizedCoreCoordinates (n : WithTop ℕ∞) {x : NormalizedState}
    (hA : 1 + x 0 ≠ 0) : ContDiffAt ℝ n normalizedCoreCoordinates x :=
  (contDiff_coreSectionCoordinates n).contDiffAt.comp x (contDiffAt_toProjectiveState n hA)

theorem contDiffAt_coreSectionChart_coordinates (n : WithTop ℕ∞) {x : NormalizedState}
    (hc : stateConstraint x = 1) (hv : projectiveActiveWall x = 1) :
    ContDiffAt ℝ n coreSectionChart (normalizedCoreCoordinates x) := by
  have hA := unit_active_wall_clock_ne_zero hv
  have hD : projectiveStateDenom (toProjectiveState x) ≠ 0 := by
    intro hzero
    have H := projective_inverse_scale hA hc
    change 6 / projectiveStateDenom (toProjectiveState x) = 1 + x 0 at H
    rw [hzero, div_zero] at H
    exact hA H.symm
  have hD' : projectiveStateDenom (coreSectionEmbedding (normalizedCoreCoordinates x)) ≠ 0 := by
    simpa only [normalizedCoreCoordinates, coreSectionEmbedding_coordinates hv] using hD
  exact (contDiffAt_fromProjectiveState n hD').comp _ (contDiff_coreSectionEmbedding n).contDiffAt

/-- An actual transverse core hit gives a nonsingular arrival map and identifies all nearby hits. -/
theorem exists_transverse_core_arrival
    {C : SectionCoordinates → NormalizedState} {y : SectionCoordinates} {t₀ t : ℝ}
    (hC : ContDiffAt ℝ 1 C y) (hp : positiveWalls (C y))
    (hc : ∀ᶠ v in 𝓝 y, stateConstraint (C v) = 1)
    (hflux : normalizedSectionFlux (C y) (fun i => fderiv ℝ C y (Pi.single i 1)) ≠ 0)
    (ht : t ∈ normalizedMaxDomain (C y) t₀)
    (hv : projectiveActiveWall (normalizedMaxCurve (C y) t₀ t) = 1)
    (htrans : normalizedEventRate projectiveActiveWall (C y) t₀ t ≠ 0) :
    ∃ R : SectionCoordinates → SectionCoordinates, ContDiffAt ℝ 1 R y ∧
      (fderiv ℝ R y).det ≠ 0 ∧
      ∀ᶠ p : SectionCoordinates × ℝ in 𝓝 (y, t),
        projectiveActiveWall (normalizedMaxCurve (C p.1) t₀ p.2) = 1 →
          R p.1 = normalizedCoreCoordinates (normalizedMaxCurve (C p.1) t₀ p.2) := by
  have hA := unit_active_wall_clock_ne_zero hv
  obtain ⟨τ, hτ, hcτ, _, hhit, huniq, hcMap, _⟩ :=
    exists_normalized_event ht (contDiffAt_projectiveActiveWall 1 hA) htrans
  let F := fun v => normalizedMaxCurve (C v) t₀ (τ (C v))
  let R := fun v => normalizedCoreCoordinates (F v)
  have hF : ContDiffAt ℝ 1 F y := hcMap.comp y hC
  have hFy : F y = normalizedMaxCurve (C y) t₀ t := by simp only [F, hτ]
  have hR : ContDiffAt ℝ 1 R y :=
    (contDiffAt_normalizedCoreCoordinates 1 (by simpa only [hFy] using hA)).comp y hF
  have hcf : stateConstraint (F y) = 1 := by
    rw [hFy, normalizedMaxCurve_constraint ht, hc.self_of_nhds]
  have hvf : projectiveActiveWall (F y) = 1 := by rw [hFy]; exact hv
  have heq : (fun v => coreSectionChart (R v)) =ᶠ[𝓝 y] F := by
    filter_upwards [hc, hC.continuousAt.eventually hhit] with v hcv htv
    exact coreSectionChart_reconstruct ((normalizedMaxCurve_constraint htv.1).trans hcv)
      (htv.2.trans hv)
  have hdet : (fderiv ℝ R y).det ≠ 0 :=
    normalized_chart_arrival_det_ne_zero (hC.differentiableAt (by norm_num))
      ((contDiffAt_coreSectionChart_coordinates 1 hcf hvf).differentiableAt (by norm_num))
      (hR.differentiableAt (by norm_num)) (hcτ.differentiableAt (by norm_num)) hp hc
      (by rw [hτ]; exact ht) hflux heq
  refine ⟨R, hR, hdet, ?_⟩
  have hpair : Tendsto (fun p : SectionCoordinates × ℝ => (C p.1, p.2))
      (𝓝 (y, t)) (𝓝 (C y, t)) :=
    (hC.continuousAt.comp continuousAt_fst).prodMk continuousAt_snd
  filter_upwards [hpair.eventually huniq] with p hp hlevel
  have htime : τ (C p.1) = p.2 := hp.2.mp (hlevel.trans hv.symm)
  simp only [R, F, htime]

end BianchiIX
