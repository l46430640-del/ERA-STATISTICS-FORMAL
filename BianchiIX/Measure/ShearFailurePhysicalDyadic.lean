import BianchiIX.Measure.ShearFailurePhysical

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal

/-- A single statistical cap works for the Borel union of all selected dyadic physical failure layers. -/
theorem exists_restartShear_physical_failure_dyadic (hBirkhoff : Literature.BirkhoffErgodicInput ℝ) :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 20 ≤ J → ∀ σ : ℝ, 0 < σ → σ < 1 → σ * (2 * J : ℕ) < 1 →
        ∃ Bcap > (0 : ℝ), Bcap < 1 ∧ ∃ hstar > (0 : ℝ),
          ∀ h ∈ Ioc (0 : ℝ) hstar, ∀ q P : ℝ, 3 < q → 4 < P → ∃ dstar > (0 : ℝ),
            ∀ d ∈ Ioc (0 : ℝ) dstar, ∀ ε : ℝ, (0 ≤ ε ∧ ε ≤ 1 / 64) →
              let E := fun j => restartShearFailureSection h
                (q / 2 * Real.log (1 / dyadicScale d j)) (dyadicScale d j) ε P η J σ Bcap
              let C := 33 * logarithmicFluxConstant (shearFailureFluxConstant σ) σ
              (∀ j : ℕ, MeasurableSet (E j)) ∧ MeasurableSet (⋃ j : ℕ, E j) ∧
                (∑' j : ℕ, mainWallMeasure h (E j)) ≤ ENNReal.ofReal (C * d * (1 + |Real.log d|) ^ 2) ∧
                mainWallMeasure h (⋃ j : ℕ, E j) ≤ ENNReal.ofReal (C * d * (1 + |Real.log d|) ^ 2) ∧
                mainWallMeasure h (⋃ j : ℕ, E j) ≠ ⊤ ∧
                ∀ j : ℕ, ∀ n₂ n₃ : ℝ, (n₂, n₃) ∈ restartShearLabelSet ε (dyadicScale d j) P →
                  ∀ ρ ∈ Icc (dyadicScale d j) (2 * dyadicScale d j),
                    ![ρ, -Real.log n₂, -Real.log n₃] ∉ ⋃ i : ℕ, E i →
                      ∃ p : eraSurvivorDomain η J σ Bcap,
                        p.val = (restartShearAmplitudeBudget (dyadicScale d j) n₂ n₃,
                          restartShearReturnState h (q / 2 * Real.log (1 / dyadicScale d j)) n₂ n₃ ρ) ∧
                        EraStatistics (EraSurvivor.digits p) (EraSurvivor.phase p) := by
  obtain ⟨δ, hδ, hδmax, Hδ⟩ := exists_restartShear_physical_failure hBirkhoff
  refine ⟨δ, hδ, hδmax, ?_⟩
  intro η hη hηδ J hJ σ hσ hσone hσJ
  obtain ⟨Bcap, hcap, hcapone, hstar, hhstar, HH⟩ := Hδ η hη hηδ J hJ σ hσ hσone hσJ
  refine ⟨Bcap, hcap, hcapone, hstar, hhstar, ?_⟩
  intro h hh q P hq hP
  obtain ⟨astar, hastar, Ha⟩ := HH h hh q P hq hP
  refine ⟨min astar 1, lt_min hastar zero_lt_one, ?_⟩
  intro d hd ε hε E C
  have Hdata (j : ℕ) := Ha (dyadicScale d j)
    ⟨dyadicScale_pos hd.1 j, (dyadicScale_le hd.1.le j).trans (hd.2.trans (min_le_left _ _))⟩ ε hε
  have hE (j : ℕ) : MeasurableSet (E j) := (Hdata j).1
  let K := 3 * logarithmicFluxConstant (shearFailureFluxConstant σ) σ
  have hK : 0 ≤ K := mul_nonneg (by norm_num)
    (logarithmicFluxConstant_nonneg (shearFailureFluxConstant_ge_one hσ.le) hσ)
  have Hlayer (j : ℕ) : mainWallMeasure h (E j) ≤ ENNReal.ofReal
      (K * (dyadicScale d j * (1 + |Real.log (dyadicScale d j)|) ^ 2)) := by
    simpa only [E, K, mul_assoc] using (Hdata j).2.2.1
  have Hsum : (∑' j : ℕ, mainWallMeasure h (E j)) ≤ ENNReal.ofReal (C * d * (1 + |Real.log d|) ^ 2) := calc
    _ ≤ _ := ENNReal.tsum_le_tsum Hlayer
    _ ≤ _ := dyadic_flux_budget hd.1 (hd.2.trans (min_le_right _ _)) hK
    _ = _ := by congr 1; dsimp only [C, K]; ring
  have Hunion := (measure_iUnion_le E).trans Hsum
  refine ⟨hE, MeasurableSet.iUnion hE, Hsum, Hunion,
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top Hunion, ?_⟩
  intro j n₂ n₃ hl ρ hρ hn
  exact (Hdata j).2.2.2.2 n₂ n₃ hl ρ hρ (fun hbad => hn (mem_iUnion_of_mem j hbad))

end BianchiIX
