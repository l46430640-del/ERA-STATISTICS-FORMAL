import BianchiIX.Measure.RestartRadialChoice
import BianchiIX.Measure.SmallSectionBoundary

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal

/-- The closed-section formulation adds a null boundary, with exactly the same successful target and flux. -/
theorem exists_restartClosedSection_borel_restart (hBirkhoff : Literature.BirkhoffErgodicInput ℝ) :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 20 ≤ J → ∀ σ : ℝ, 0 < σ → σ < 1 → σ * (2 * J : ℕ) < 1 →
        ∃ Bcap > (0 : ℝ), Bcap < 1 ∧ ∃ hstar > (0 : ℝ), hstar ≤ 1 / 8 ∧
          ∀ h ∈ Ioc (0 : ℝ) hstar, ∀ q D P : ℝ, 3 < q → 4 < D → 6 * D + 2 < P →
            ∀ ε ∈ Ioc (0 : ℝ) (1 / 128), ∃ C > (0 : ℝ),
              ∀ Bbound : ℝ, 0 < Bbound → ∃ dstar > (0 : ℝ), dstar ≤ h / 8 ∧
                ∀ d ∈ Ioc (0 : ℝ) dstar,
                  let F := restartRadialFailureFamily h q d ε P η J σ Bcap
                  let E := mainWallClosedFailure d (radialFailureSet d ε F)
                  MeasurableSet E ∧ E ⊆ mainWallSmallSection d ∧
                    mainWallOriginalMeasure h E = (∑' i, radialFailureIntegral h d ε F i) ∧
                    mainWallMeasure h E ≤ mainWallOriginalMeasure h E ∧
                    mainWallOriginalMeasure h E ≤ ENNReal.ofReal (C * d * (1 + |Real.log d|) ^ 2) ∧
                    mainWallOriginalMeasure h E ≠ ⊤ ∧
                    ∃ W : SectionCoordinates → CoreRestartData, Measurable W ∧
                      ∀ y ∈ mainWallSmallSection d \ E,
                        y ∈ mainWallChartDomain h ∧ (W y).2.1 ≤ Bbound ∧
                        CoreRestartWitness η J σ Bcap (mainWallChart h y) (W y) ∧
                        ∃ i : RadialPieceIndex, y ∈ physicalRadialPiece d ε i ∧
                          (W y).2 = restartRadialOutput h q d ε i (radialPieceInverse i.1 y) := by
  obtain ⟨δ, hδ, hδmax, Hδ⟩ := exists_restartRadialFailure_borel_restart hBirkhoff
  refine ⟨δ, hδ, hδmax, ?_⟩
  intro η hη hηδ J hJ σ hσ hσ1 hσJ
  obtain ⟨Bcap, hcap, hcap1, hstar, hhstar, hh1, HH⟩ := Hδ η hη hηδ J hJ σ hσ hσ1 hσJ
  refine ⟨Bcap, hcap, hcap1, hstar, hhstar, hh1, ?_⟩
  intro h hh q D P hq hD hP ε hε
  obtain ⟨C, hC, HC⟩ := HH h hh q D P hq hD hP ε hε
  refine ⟨C, hC, ?_⟩
  intro Bbound hBbound
  obtain ⟨dstar, hdstar, hdh, HD⟩ := HC Bbound hBbound
  refine ⟨dstar, hdstar, hdh, ?_⟩
  intro d hd F E
  obtain ⟨_, hF, Heq, Hbound, Hfin, W, hW, HW⟩ := HD d hd
  have hmeasure : mainWallOriginalMeasure h E = mainWallOriginalMeasure h (radialFailureSet d ε F) :=
    mainWallOriginalMeasure_closedFailure h d _
  refine ⟨measurableSet_mainWallClosedFailure d hF,
    mainWallClosedFailure_subset (radialFailureSet_subset_openSection hd.1 (by linarith only [hε.2]) F),
    hmeasure.trans Heq, mainWallMeasure_le_original hh.1 E,
    hmeasure.trans_le Hbound, hmeasure ▸ Hfin, W, hW, ?_⟩
  intro y hy
  exact HW y (by rwa [mainWallClosedFailure_complement] at hy)

end BianchiIX
