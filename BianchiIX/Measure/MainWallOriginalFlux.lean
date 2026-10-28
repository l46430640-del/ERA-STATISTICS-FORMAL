import BianchiIX.Measure.RestartClosedSection
import BianchiIX.Measure.OriginalSectionMeasure

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal

theorem mainWallSmallSection_subset_chart {h d : ℝ} (hh : 0 < h) (hh1 : h ≤ 1 / 8)
    (hdh : d ≤ h / 8) : mainWallSmallSection d ⊆ mainWallChartDomain h := by
  intro z hz
  exact mainWallChartDomain_of_small hh hh1 hdh hz.1
    ((le_max_left _ _).trans hz.2) ((le_max_right _ _).trans hz.2)

/-- The original and corrected fluxes of a restricted failure set are uniformly comparable. -/
theorem mainWallOriginalMeasure_small_failure {h d : ℝ} (hh : 0 < h) (hdh : d ≤ h)
    {F : Set SectionCoordinates} (hF : MeasurableSet F) :
    mainWallMeasure h (mainWallSmallSection d ∩ F) ≤ mainWallOriginalMeasure h (mainWallSmallSection d ∩ F) ∧
      mainWallOriginalMeasure h (mainWallSmallSection d ∩ F) ≤
        ENNReal.ofReal (1 + 4 * h ^ 2) * mainWallMeasure h F := by
  refine ⟨mainWallMeasure_le_original hh _, ?_⟩
  have H := mainWallOriginalMeasure_le_of_small_walls hh
    ((measurableSet_mainWallSmallSection d).inter hF)
    (fun z hz => ⟨(le_max_left _ _).trans (hz.1.2.trans hdh),
      (le_max_right _ _).trans (hz.1.2.trans hdh)⟩)
  exact H.trans (mul_le_mul' le_rfl (measure_mono inter_subset_right))

/-- The same original-flux failure set has a uniform quantitative bound and a jointly Borel actual restart. -/
theorem exists_mainWallRegion_borel_restart_original_quantitative (hBirkhoff : Literature.BirkhoffErgodicInput ℝ) :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 20 ≤ J → ∀ σ : ℝ, 0 < σ → σ < 1 → σ * (2 * J : ℕ) < 1 →
        ∃ Bcap > (0 : ℝ), Bcap < 1 ∧ ∃ hstar > (0 : ℝ), hstar ≤ 1 / 128 ∧
          ∀ h ∈ Ioc (0 : ℝ) hstar, ∀ q D P : ℝ, 3 < q → 4 < D → 6 * D + 2 < P →
            ∃ C > (0 : ℝ), ∀ Bbound : ℝ, 0 < Bbound →
              ∃ dstar > (0 : ℝ), dstar < h / 8 ∧ ∀ d ∈ Ioc (0 : ℝ) dstar,
              ∃ F : Set SectionCoordinates, MeasurableSet F ∧
                F ⊆ mainWallSmallSection d ∩ mainWallChartDomain h ∧
                mainWallMeasure h F ≤ mainWallOriginalMeasure h F ∧
                mainWallOriginalMeasure h F ≤ ENNReal.ofReal (C * d * (1 + |Real.log d|) ^ 2) ∧
                mainWallOriginalMeasure h F ≠ ⊤ ∧
                ∃ W : SectionCoordinates → CoreRestartData, Measurable W ∧
                  ∀ z ∈ mainWallSmallSection d \ F, z ∈ mainWallChartDomain h ∧ (W z).2.1 ≤ Bbound ∧
                    CoreRestartWitness η J σ Bcap (mainWallChart h z) (W z) := by
  obtain ⟨δ, hδ, hδmax, Hδ⟩ := exists_restartClosedSection_borel_restart hBirkhoff
  refine ⟨δ, hδ, hδmax, ?_⟩
  intro η hη hηδ J hJ σ hσ hσone hσJ
  obtain ⟨Bcap, hcap, hcapone, hS, hhS, _, HS⟩ := Hδ η hη hηδ J hJ σ hσ hσone hσJ
  refine ⟨Bcap, hcap, hcapone, min hS (1 / 128), lt_min hhS (by norm_num), min_le_right _ _, ?_⟩
  intro h hh q D P hq hD hP
  obtain ⟨C, hC, HC⟩ := HS h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q D P hq hD hP
    (1 / 128) (by norm_num)
  have hh1 : h ≤ 1 / 128 := hh.2.trans (min_le_right _ _)
  refine ⟨C, hC, ?_⟩
  intro Bbound hBbound
  obtain ⟨dS, hdS, _, HdS⟩ := HC Bbound hBbound
  refine ⟨min dS (h / 16), lt_min hdS (div_pos hh.1 (by norm_num)),
    (min_le_right _ _).trans_lt (by linarith only [hh.1]), ?_⟩
  intro d hd
  have hdh : d ≤ h / 16 := hd.2.trans (min_le_right _ _)
  obtain ⟨hF, hsub, _, hcompare, Hbound, Hfin, W, hW, Hgood⟩ :=
    HdS d ⟨hd.1, hd.2.trans (min_le_left _ _)⟩
  refine ⟨_, hF, fun z hz => ⟨hsub hz, mainWallSmallSection_subset_chart hh.1 (by linarith only [hh1])
      (by linarith only [hdh, hh.1]) (hsub hz)⟩,
    hcompare, Hbound, Hfin, W, hW, ?_⟩
  intro z hz
  exact ⟨(Hgood z hz).1, (Hgood z hz).2.1, (Hgood z hz).2.2.1⟩

/-- A quantitative bound for the actual statistical success set in the original flux. -/
theorem exists_mainWallRegion_original_statistics (hBirkhoff : Literature.BirkhoffErgodicInput ℝ) :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 20 ≤ J → ∀ σ : ℝ, 0 < σ → σ < 1 → σ * (2 * J : ℕ) < 1 →
        ∃ Bcap > (0 : ℝ), Bcap < 1 ∧ ∃ hstar > (0 : ℝ), hstar ≤ 1 / 128 ∧
          ∀ h ∈ Ioc (0 : ℝ) hstar, ∀ q D P : ℝ, 3 < q → 4 < D → 6 * D + 2 < P →
            ∃ dstar > (0 : ℝ), dstar < h / 8 ∧ ∃ C > (0 : ℝ), ∀ d ∈ Ioc (0 : ℝ) dstar,
              ∃ F : Set SectionCoordinates, MeasurableSet F ∧
                F ⊆ mainWallSmallSection d ∩ mainWallChartDomain h ∧
                mainWallMeasure h F ≤ mainWallOriginalMeasure h F ∧
                mainWallOriginalMeasure h F ≤ ENNReal.ofReal (C * d * (1 + |Real.log d|) ^ 2) ∧
                mainWallOriginalMeasure h F ≠ ⊤ ∧
                ∀ z ∈ mainWallSmallSection d \ F,
                  z ∈ mainWallChartDomain h ∧ StatisticalCoreFuture η J σ Bcap (mainWallChart h z) := by
  obtain ⟨δ, hδ, hδmax, Hδ⟩ := exists_mainWallRegion_borel_restart_original_quantitative hBirkhoff
  refine ⟨δ, hδ, hδmax, ?_⟩
  intro η hη hηδ J hJ σ hσ hσone hσJ
  obtain ⟨Bcap, hcap, hcapone, hS, hhS, hh128, HS⟩ := Hδ η hη hηδ J hJ σ hσ hσone hσJ
  refine ⟨Bcap, hcap, hcapone, hS, hhS, hh128, ?_⟩
  intro h hh q D P hq hD hP
  obtain ⟨C, hC, HC⟩ := HS h hh q D P hq hD hP
  obtain ⟨dS, hdS, hdh, HdS⟩ := HC 1 zero_lt_one
  refine ⟨dS, hdS, hdh, C, hC, ?_⟩
  intro d hd
  obtain ⟨F, hF, hsub, hcompare, hbound, hfinite, W, _, HW⟩ := HdS d hd
  refine ⟨F, hF, hsub, hcompare, hbound, hfinite, ?_⟩
  intro z hz
  have H := HW z hz
  exact ⟨H.1, H.2.2.statisticalCoreFuture⟩

/-- The same jointly Borel actual restart remains valid with a finite original-flux failure set. -/
theorem exists_mainWallRegion_borel_restart_original_flux (hBirkhoff : Literature.BirkhoffErgodicInput ℝ) :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 20 ≤ J → ∀ σ : ℝ, 0 < σ → σ < 1 → σ * (2 * J : ℕ) < 1 →
        ∃ Bcap > (0 : ℝ), Bcap < 1 ∧ ∃ hstar > (0 : ℝ),
          ∀ h ∈ Ioc (0 : ℝ) hstar, ∀ q D P : ℝ, 3 < q → 4 < D → 6 * D + 2 < P →
            ∀ Bbound : ℝ, 0 < Bbound → ∃ dstar > (0 : ℝ), ∀ d ∈ Ioc (0 : ℝ) dstar,
              ∃ F : Set SectionCoordinates, MeasurableSet F ∧ F ⊆ mainWallSmallSection d ∧
                mainWallOriginalMeasure h F ≠ ⊤ ∧
                ∃ W : SectionCoordinates → CoreRestartData, Measurable W ∧
                  ∀ z ∈ mainWallSmallSection d \ F, z ∈ mainWallChartDomain h ∧ (W z).2.1 ≤ Bbound ∧
                    CoreRestartWitness η J σ Bcap (mainWallChart h z) (W z) := by
  obtain ⟨δ, hδ, hδmax, Hδ⟩ := exists_mainWallRegion_borel_restart_original_quantitative hBirkhoff
  refine ⟨δ, hδ, hδmax, ?_⟩
  intro η hη hηδ J hJ σ hσ hσone hσJ
  obtain ⟨Bcap, hcap, hcapone, hS, hhS, _, HS⟩ := Hδ η hη hηδ J hJ σ hσ hσone hσJ
  refine ⟨Bcap, hcap, hcapone, hS, hhS, ?_⟩
  intro h hh q D P hq hD hP Bbound hBbound
  obtain ⟨_, _, HC⟩ := HS h hh q D P hq hD hP
  obtain ⟨dS, hdS, _, HdS⟩ := HC Bbound hBbound
  refine ⟨dS, hdS, ?_⟩
  intro d hd
  obtain ⟨F, hF, hsub, _, _, hfinite, H⟩ := HdS d hd
  exact ⟨F, hF, hsub.trans inter_subset_left, hfinite, H⟩

end BianchiIX
