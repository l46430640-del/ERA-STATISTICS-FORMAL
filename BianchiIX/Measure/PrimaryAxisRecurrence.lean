import BianchiIX.Measure.LateAxisSection
import BianchiIX.Measure.AxisStatisticalCapture
import BianchiIX.Measure.MainWallRegionStatistics

noncomputable section

namespace BianchiIX

open Set Filter MeasureTheory
open scoped Topology ENNReal

/-- The complete small three-axis section has infinitely many genuine future returns almost everywhere under wall-product decay. -/
theorem ae_primaryAxis_infiniteReturns_of_decay
    (hBirkhoff : Literature.BirkhoffErgodicInput ℝ) {h d : ℝ}
    (hh : 0 < h) (hhmax : h ≤ 1 / 16) (hd : 0 < d) (hdh : d < h / 8) :
    let E := fun _ : Fin 3 => mainWallSmallSection d ∩ mainWallChartDomain h
    ∀ᵐ z ∂axisFamilyMeasure (fun _ : Fin 3 => h), z ∈ axisFamilySection E →
      (∀ i j : Fin 3, i ≠ j → Tendsto
        (fun t => wallValue i (normalizedMaxCurve (axisFamilyChart primaryAxisFrame (fun _ => h) z) 0 t) *
          wallValue j (normalizedMaxCurve (axisFamilyChart primaryAxisFrame (fun _ => h) z) 0 t))
            atTop (𝓝 0)) →
      z ∈ axisFamilyInfiniteReturns primaryAxisFrame (fun _ => h) 0 E := by
  intro E
  rw [ae_axisFamilyMeasure_iff]
  intro a
  have hflux (y : SectionCoordinates) (hy : y ∈ mainWallChartDomain h) :
      normalizedSectionFlux (axisWallChart (primaryAxisFrame a) h y)
        (fun i => fderiv ℝ (axisWallChart (primaryAxisFrame a) h) y (Pi.single i 1)) ≠ 0 := by
    change normalizedSectionFlux (axisWallChart (primaryAxisFrame a) h y)
      (axisWallChartFrame (primaryAxisFrame a) h y) ≠ 0
    rw [axisWallChart_signed_flux (primaryAxisFrame a) hh hy]
    exact neg_ne_zero.mpr (mainWallChartDensity_pos hh hy).ne'
  have H := ae_transverse_late_primaryAxis_crossing hBirkhoff hh hhmax hd hdh
    (isOpen_mainWallChartDomain h) (fun y hy => contDiffAt_axisWallChart (primaryAxisFrame a) hy 1)
    (fun y _ => axisWallChart_positive (primaryAxisFrame a) hh y)
    (fun _ hy => axisWallChart_constraint (primaryAxisFrame a) hy) hflux
    1
  rw [withDensity_one] at H
  filter_upwards [(mainWallMeasure_absolutelyContinuous h).ae_le (ae_restrict_of_ae H)] with y hy hz hprod
  refine ⟨hz, infinite_of_not_bddAbove ?_⟩
  obtain ⟨i, hi⟩ := hy hz.2 hprod
  rw [not_bddAbove_iff]
  intro R
  obtain ⟨c, hcR, _, w, hw, hchart, hs, hb, hc, _⟩ := hi R 1 (by norm_num)
  refine ⟨c, ?_, (le_max_left R 0).trans_lt hcR⟩
  rw [axisFamily_returnTimes_eq_physical_hits (fun _ => hh) (fun _ _ hw => hw.2)]
  refine ⟨(le_max_right R 0).trans_lt hcR, hz.2, (i, w), ?_, hchart⟩
  exact ⟨⟨hs.le, max_le hb.le hc.le⟩, hw⟩

end BianchiIX
