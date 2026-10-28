import BianchiIX.Measure.LateAwaySectionNull
import BianchiIX.Measure.TaubSubspaceNull
import BianchiIX.Dynamics.LateAxisCrossing

noncomputable section

namespace BianchiIX

open Set Filter MeasureTheory
open scoped Topology ENNReal

/-- On every transverse chart, decaying wall products imply arbitrarily late small-section crossings almost everywhere. -/
theorem ae_transverse_late_primaryAxis_crossing
    (hBirkhoff : Literature.BirkhoffErgodicInput ℝ) {h d : ℝ}
    (hh : 0 < h) (hhmax : h ≤ 1 / 16) (hd : 0 < d) (hdh : d < h / 8)
    {C : SectionCoordinates → NormalizedState} {U : Set SectionCoordinates}
    (hU : IsOpen U) (hC : ∀ y ∈ U, ContDiffAt ℝ 1 C y)
    (hp : ∀ y ∈ U, positiveWalls (C y)) (hc : ∀ y ∈ U, stateConstraint (C y) = 1)
    (hflux : ∀ y ∈ U,
      normalizedSectionFlux (C y) (fun i => fderiv ℝ C y (Pi.single i 1)) ≠ 0)
    (ρ : SectionCoordinates → ℝ≥0∞) :
    ∀ᵐ y ∂(volume.withDensity ρ), y ∈ U →
      (∀ i j : Fin 3, i ≠ j → Tendsto
        (fun t => wallValue i (normalizedMaxCurve (C y) 0 t) * wallValue j (normalizedMaxCurve (C y) 0 t))
          atTop (𝓝 0)) →
      ∃ i : Fin 3, ∀ R : ℝ, ∀ η > (0 : ℝ), ∃ c > max R 0,
        c ∈ normalizedMaxDomain (C y) 0 ∧ ∃ z ∈ mainWallChartDomain h,
          axisWallChart (primaryAxisFrame i) h z = normalizedMaxCurve (C y) 0 c ∧
          |z 0| < d ∧ Real.exp (-z 1) < d ∧ Real.exp (-z 2) < d ∧
          normalizedTaubRadiusSq ((primaryAxisFrame i).map (normalizedMaxCurve (C y) 0 c)) < η := by
  filter_upwards [ae_arbitrarily_late_taub_approach hBirkhoff hU hC hp hc hflux ρ,
    ae_primaryAxis_taubRadiusSq_pos hC hflux ρ] with y hvisit hr hy hprod
  exact exists_arbitrarily_late_primaryAxis_crossing (hc y hy) (hp y hy) (hr hy)
    hh hhmax hd hdh hprod (hvisit hy hprod)

end BianchiIX
