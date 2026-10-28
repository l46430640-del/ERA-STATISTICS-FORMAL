import BianchiIX.Measure.MainWallRegionStatistics
import BianchiIX.Measure.StatisticalCapture

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal

/-- Almost every orbit with infinitely many returns to the full small main-wall section has a statistical core in its exact future. -/
theorem exists_mainWallRegion_capture (hBirkhoff : Literature.BirkhoffErgodicInput ℝ) :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 20 ≤ J → ∀ σ : ℝ, 0 < σ → σ < 1 → σ * (2 * J : ℕ) < 1 →
        ∃ Bcap > (0 : ℝ), Bcap < 1 ∧ ∃ hstar > (0 : ℝ),
          ∀ h ∈ Ioc (0 : ℝ) hstar, ∃ dstar > (0 : ℝ), ∀ d ∈ Ioc (0 : ℝ) dstar,
            let B := mainWallSmallSection d ∩ mainWallChartDomain h
            MeasurableSet B ∧
              ∀ᵐ z ∂mainWallMeasure h, z ∈ mainWallInfiniteReturns h 0 B →
                StatisticalCoreFuture η J σ Bcap (mainWallChart h z) := by
  obtain ⟨δ, hδ, hδmax, Hδ⟩ := exists_mainWallRegion_statistics hBirkhoff
  refine ⟨δ, hδ, hδmax, ?_⟩
  intro η hη hηδ J hJ σ hσ hσone hσJ
  obtain ⟨Bcap, hcap, hcapone, hS, hhS, HS⟩ := Hδ η hη hηδ J hJ σ hσ hσone hσJ
  refine ⟨Bcap, hcap, hcapone, min hS (1 / 8), lt_min hhS (by norm_num), ?_⟩
  intro h hh
  have hh1 : h ≤ 1 / 8 := hh.2.trans (min_le_right _ _)
  obtain ⟨dS, hdS, _, _, HdS⟩ := HS h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩
    50 90 550 (by norm_num) (by norm_num) (by norm_num)
  refine ⟨min dS (h / 8), lt_min hdS (div_pos hh.1 (by norm_num)), ?_⟩
  intro d hd B
  have hdh : d ≤ h / 8 := hd.2.trans (min_le_right _ _)
  obtain ⟨F, hF, _, hfinite, Hgood⟩ := HdS d ⟨hd.1, hd.2.trans (min_le_left _ _)⟩
  have hB : MeasurableSet B := (measurableSet_mainWallSmallSection d).inter
    (isOpen_mainWallChartDomain h).measurableSet
  have hbound (z : SectionCoordinates) (hz : z ∈ B) : mainWallChart h z 0 ≤ -(15 / 16) := by
    have hs : |z 0| ≤ 1 / 8 := hz.1.1.trans (by linarith only [hdh, hh1])
    have h₂ : Real.exp (-z 1) ≤ h / 8 := (le_max_left _ _).trans (hz.1.2.trans hdh)
    have h₃ : Real.exp (-z 2) ≤ h / 8 := (le_max_right _ _).trans (hz.1.2.trans hdh)
    exact mainWall_small_target_shear hh.1 hh1 hz.2 hs h₂ h₃
  exact ⟨hB, ae_mainWall_statistical_future hh.1 (by norm_num : (0 : ℝ) < 15 / 16)
    hbound hB hF hfinite (fun z hz => (Hgood z ⟨hz.1.1, hz.2⟩).2)⟩

end BianchiIX
