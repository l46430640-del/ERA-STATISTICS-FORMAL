import BianchiIX.Measure.MainWallRegionStatistics
import BianchiIX.Measure.AxisStatisticalCapture

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal

/-- The complete three-axis small section has finite exceptional flux and captures almost every infinitely returning orbit. -/
theorem exists_mainWall_primaryAxis_capture (hBirkhoff : Literature.BirkhoffErgodicInput ℝ) :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 20 ≤ J → ∀ σ : ℝ, 0 < σ → σ < 1 → σ * (2 * J : ℕ) < 1 →
        ∃ Bcap > (0 : ℝ), Bcap < 1 ∧ ∃ hstar > (0 : ℝ),
          ∀ h ∈ Ioc (0 : ℝ) hstar, ∃ dstar > (0 : ℝ), ∃ C > (0 : ℝ),
            ∀ d ∈ Ioc (0 : ℝ) dstar,
              let B := mainWallSmallSection d ∩ mainWallChartDomain h
              let E := fun _ : Fin 3 => B
              ∃ F : Set (Fin 3 × SectionCoordinates),
                MeasurableSet B ∧ MeasurableSet F ∧
                  InjOn (axisFamilyChart primaryAxisFrame (fun _ => h)) (axisFamilySection E) ∧
                  axisFamilyMeasure (fun _ : Fin 3 => h) F ≤
                    ENNReal.ofReal (3 * C * d * (1 + |Real.log d|) ^ 2) ∧
                  axisFamilyMeasure (fun _ : Fin 3 => h) F ≠ ⊤ ∧
                  (∀ z ∈ axisFamilySection E \ F,
                    StatisticalCoreFuture η J σ Bcap (axisFamilyChart primaryAxisFrame (fun _ => h) z)) ∧
                  ∀ᵐ z ∂axisFamilyMeasure (fun _ : Fin 3 => h),
                    z ∈ axisFamilyInfiniteReturns primaryAxisFrame (fun _ => h) 0 E →
                      StatisticalCoreFuture η J σ Bcap (axisFamilyChart primaryAxisFrame (fun _ => h) z) := by
  obtain ⟨δ, hδ, hδmax, Hδ⟩ := exists_mainWallRegion_statistics hBirkhoff
  refine ⟨δ, hδ, hδmax, ?_⟩
  intro η hη hηδ J hJ σ hσ hσone hσJ
  obtain ⟨Bcap, hcap, hcapone, hS, hhS, HS⟩ := Hδ η hη hηδ J hJ σ hσ hσone hσJ
  refine ⟨Bcap, hcap, hcapone, min hS (1 / 8), lt_min hhS (by norm_num), ?_⟩
  intro h hh
  obtain ⟨dS, hdS, C, hC, HdS⟩ := HS h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩
    50 90 550 (by norm_num) (by norm_num) (by norm_num)
  refine ⟨min dS (h / 8), lt_min hdS (div_pos hh.1 (by norm_num)), C, hC, ?_⟩
  intro d hd B E
  have hh1 : h ≤ 1 / 8 := hh.2.trans (min_le_right _ _)
  have hdh : d ≤ h / 8 := hd.2.trans (min_le_right _ _)
  have hd1 : d ≤ 1 / 8 := hdh.trans (by linarith only [hh1])
  obtain ⟨F₀, hF₀, Hbound, _, Hgood⟩ := HdS d ⟨hd.1, hd.2.trans (min_le_left _ _)⟩
  let F := axisFamilySection (fun _ : Fin 3 => F₀)
  have hB : MeasurableSet B :=
    (measurableSet_mainWallSmallSection d).inter (isOpen_mainWallChartDomain h).measurableSet
  have hF : MeasurableSet F := measurableSet_axisFamilySection (fun _ => hF₀)
  have hsmall (i : Fin 3) (y : SectionCoordinates) (hy : y ∈ E i) :
      y ∈ mainWallChartDomain h ∧ |y 0| ≤ 1 / 8 ∧ Real.exp (-y 1) ≤ h / 8 ∧ Real.exp (-y 2) ≤ h / 8 :=
    ⟨hy.2, hy.1.1.trans hd1,
      (le_max_left _ _).trans (hy.1.2.trans hdh), (le_max_right _ _).trans (hy.1.2.trans hdh)⟩
  have hinj : InjOn (axisFamilyChart primaryAxisFrame (fun _ => h)) (axisFamilySection E) :=
    primaryAxisChart_injOn (fun i y hy => mem_dominantWallChartDomain_of_small hh.1
      (hsmall i y hy).1 (hsmall i y hy).2.2.1 (hsmall i y hy).2.2.2)
  have Hthree : axisFamilyMeasure (fun _ : Fin 3 => h) F ≤
      ENNReal.ofReal (3 * C * d * (1 + |Real.log d|) ^ 2) := calc
    _ = 3 * mainWallMeasure h F₀ := by
      simpa only [Fintype.card_fin, Nat.cast_ofNat] using axisFamilyMeasure_constant_section (ι := Fin 3) h hF₀
    _ ≤ 3 * ENNReal.ofReal (C * d * (1 + |Real.log d|) ^ 2) := mul_le_mul' le_rfl Hbound
    _ = _ := by
      rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)]
      congr 1
      ring
  have hfinite := ne_top_of_le_ne_top ENNReal.ofReal_ne_top Hthree
  have hgood (z : Fin 3 × SectionCoordinates) (hz : z ∈ axisFamilySection E \ F) :
      StatisticalCoreFuture η J σ Bcap (mainWallChart h z.2) := (Hgood z.2 ⟨hz.1.1, hz.2⟩).2
  refine ⟨F, hB, hF, hinj, Hthree, hfinite, ?_, ?_⟩
  · intro z hz
    exact (statisticalCoreFuture_axisWallChart_iff (Equiv.swap 0 z.1) z.2).mpr (hgood z hz)
  · exact ae_primaryAxis_statistical_future hh.1 hh1 (fun _ => hB) hsmall hF hfinite hgood

end BianchiIX
