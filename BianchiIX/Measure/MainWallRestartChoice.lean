import BianchiIX.Measure.RestartClosedSection

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal

/-- One fixed failure set has both the quantitative flux bound and a jointly Borel actual restart. -/
theorem exists_mainWallRegion_borel_restart_quantitative (hBirkhoff : Literature.BirkhoffErgodicInput ℝ) :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 20 ≤ J → ∀ σ : ℝ, 0 < σ → σ < 1 → σ * (2 * J : ℕ) < 1 →
        ∃ Bcap > (0 : ℝ), Bcap < 1 ∧ ∃ hstar > (0 : ℝ),
          ∀ h ∈ Ioc (0 : ℝ) hstar, ∀ q D P : ℝ, 3 < q → 4 < D → 6 * D + 2 < P →
            ∃ C > (0 : ℝ), ∀ Bbound : ℝ, 0 < Bbound → ∃ dstar > (0 : ℝ), ∀ d ∈ Ioc (0 : ℝ) dstar,
              ∃ F : Set SectionCoordinates, MeasurableSet F ∧
                mainWallMeasure h F ≤ ENNReal.ofReal (C * d * (1 + |Real.log d|) ^ 2) ∧ mainWallMeasure h F ≠ ⊤ ∧
                ∃ W : SectionCoordinates → CoreRestartData, Measurable W ∧
                  ∀ z ∈ mainWallSmallSection d \ F, z ∈ mainWallChartDomain h ∧ (W z).2.1 ≤ Bbound ∧
                    CoreRestartWitness η J σ Bcap (mainWallChart h z) (W z) := by
  obtain ⟨δ, hδ, hδmax, Hδ⟩ := exists_restartClosedSection_borel_restart hBirkhoff
  refine ⟨δ, hδ, hδmax, ?_⟩
  intro η hη hηδ J hJ σ hσ hσone hσJ
  obtain ⟨Bcap, hcap, hcapone, hS, hhS, _, HS⟩ := Hδ η hη hηδ J hJ σ hσ hσone hσJ
  refine ⟨Bcap, hcap, hcapone, hS, hhS, ?_⟩
  intro h hh q D P hq hD hP
  obtain ⟨C, hC, HC⟩ := HS h hh q D P hq hD hP (1 / 128) (by norm_num)
  refine ⟨C, hC, ?_⟩
  intro Bbound hBbound
  obtain ⟨dS, hdS, _, HdS⟩ := HC Bbound hBbound
  refine ⟨dS, hdS, ?_⟩
  intro d hd
  obtain ⟨hF, _, _, hcompare, Hbound, Hfin, W, hW, HW⟩ := HdS d hd
  refine ⟨_, hF, hcompare.trans Hbound, ne_top_of_le_ne_top Hfin hcompare, W, hW, ?_⟩
  intro z hz
  exact ⟨(HW z hz).1, (HW z hz).2.1, (HW z hz).2.2.1⟩

/-- The entire small main-wall success section has one Borel restart with a common statistical cap. -/
theorem exists_mainWallRegion_borel_restart (hBirkhoff : Literature.BirkhoffErgodicInput ℝ) :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 20 ≤ J → ∀ σ : ℝ, 0 < σ → σ < 1 → σ * (2 * J : ℕ) < 1 →
        ∃ Bcap > (0 : ℝ), Bcap < 1 ∧ ∃ hstar > (0 : ℝ),
          ∀ h ∈ Ioc (0 : ℝ) hstar, ∀ q D P : ℝ, 3 < q → 4 < D → 6 * D + 2 < P →
            ∀ Bbound : ℝ, 0 < Bbound → ∃ dstar > (0 : ℝ), ∀ d ∈ Ioc (0 : ℝ) dstar,
              ∃ F : Set SectionCoordinates, MeasurableSet F ∧ mainWallMeasure h F ≠ ⊤ ∧
                ∃ W : SectionCoordinates → CoreRestartData, Measurable W ∧
                  ∀ z ∈ mainWallSmallSection d \ F, z ∈ mainWallChartDomain h ∧ (W z).2.1 ≤ Bbound ∧
                    CoreRestartWitness η J σ Bcap (mainWallChart h z) (W z) := by
  obtain ⟨δ, hδ, hδmax, Hδ⟩ := exists_mainWallRegion_borel_restart_quantitative hBirkhoff
  refine ⟨δ, hδ, hδmax, ?_⟩
  intro η hη hηδ J hJ σ hσ hσone hσJ
  obtain ⟨Bcap, hcap, hcapone, hS, hhS, HS⟩ := Hδ η hη hηδ J hJ σ hσ hσone hσJ
  refine ⟨Bcap, hcap, hcapone, hS, hhS, ?_⟩
  intro h hh q D P hq hD hP Bbound hBbound
  obtain ⟨_, _, H⟩ := HS h hh q D P hq hD hP
  obtain ⟨dS, hdS, HdS⟩ := H Bbound hBbound
  refine ⟨dS, hdS, ?_⟩
  intro d hd
  obtain ⟨F, hF, _, HF⟩ := HdS d hd
  exact ⟨F, hF, HF⟩

end BianchiIX
