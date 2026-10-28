import BianchiIX.Measure.AngularFailurePhysical

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal

theorem exists_restartAngular_physical_failure_dyadic (hBirkhoff : Literature.BirkhoffErgodicInput ℝ) :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 20 ≤ J → ∀ σ : ℝ, 0 < σ → σ < 1 → σ * (2 * J : ℕ) < 1 →
        ∃ Bcap > (0 : ℝ), Bcap < 1 ∧ ∃ hstar > (0 : ℝ),
          ∀ h ∈ Ioc (0 : ℝ) hstar, ∀ L : ℝ, 0 ≤ L →
            ∀ q P : ℝ, 3 < q → 4 < P → ∃ dstar > (0 : ℝ),
              ∀ d ∈ Ioc (0 : ℝ) dstar,
                let E := fun j => restartAngularFailureSection h (q / 2 * Real.log (1 / dyadicScale d j))
                  (dyadicScale d j) L P η J σ Bcap
                let K := 6 * L * logarithmicFluxConstantOne (angularFailureFluxConstant L σ) σ
                (∀ j : ℕ, MeasurableSet (E j)) ∧ MeasurableSet (⋃ j : ℕ, E j) ∧
                  (∑' j : ℕ, mainWallMeasure h (E j)) ≤ ENNReal.ofReal (K * d * (1 + |Real.log d| + 2 * Real.log 2)) ∧
                  mainWallMeasure h (⋃ j : ℕ, E j) ≤ ENNReal.ofReal (K * d * (1 + |Real.log d| + 2 * Real.log 2)) ∧
                  mainWallMeasure h (⋃ j : ℕ, E j) ≠ ⊤ ∧
                  ∀ j : ℕ, ∀ θ ζ : ℝ, |θ| ≤ L → (0 < ζ ∧ ζ ≤ (dyadicScale d j) ^ P) →
                    ∀ ρ ∈ Icc (dyadicScale d j) (2 * dyadicScale d j),
                      ![θ * ρ, -Real.log ρ, -Real.log ζ] ∉ ⋃ i : ℕ, E i →
                        ∃ p : eraSurvivorDomain η J σ Bcap,
                          p.val = (restartAmplitudeBudget L (dyadicScale d j) ζ,
                            restartReturnState h (q / 2 * Real.log (1 / dyadicScale d j)) θ ζ ρ) ∧
                          EraStatistics (EraSurvivor.digits p) (EraSurvivor.phase p) := by
  obtain ⟨δ, hδ, hδmax, Hδ⟩ := exists_restartAngular_physical_failure hBirkhoff
  refine ⟨δ, hδ, hδmax, ?_⟩
  intro η hη hηδ J hJ σ hσ hσone hσJ
  obtain ⟨Bcap, hcap, hcapone, hstar, hhstar, HH⟩ := Hδ η hη hηδ J hJ σ hσ hσone hσJ
  refine ⟨Bcap, hcap, hcapone, hstar, hhstar, ?_⟩
  intro h hh L hL q P hq hP
  obtain ⟨astar, hastar, Ha⟩ := HH h hh L hL q P hq hP
  refine ⟨min astar 1, lt_min hastar zero_lt_one, ?_⟩
  intro d hd E K
  have Hdata (j : ℕ) := Ha (dyadicScale d j)
    ⟨dyadicScale_pos hd.1 j, (dyadicScale_le hd.1.le j).trans (hd.2.trans (min_le_left _ _))⟩
  have hE (j : ℕ) : MeasurableSet (E j) := (Hdata j).1
  have hK : 0 ≤ K := mul_nonneg (mul_nonneg (by norm_num) hL)
    (logarithmicFluxConstantOne_nonneg (angularFailureFluxConstant_ge_one hL hσ.le) hσ)
  have Hlayer (j : ℕ) : mainWallMeasure h (E j) ≤ ENNReal.ofReal
      (K * (dyadicScale d j * (1 + |Real.log (dyadicScale d j)|))) := by
    simpa only [E, K, mul_assoc] using (Hdata j).2.1
  have Hsum : (∑' j : ℕ, mainWallMeasure h (E j)) ≤
      ENNReal.ofReal (K * d * (1 + |Real.log d| + 2 * Real.log 2)) :=
    (ENNReal.tsum_le_tsum Hlayer).trans_eq (dyadic_log_one_flux_sum hd.1 (hd.2.trans (min_le_right _ _)) hK)
  have Hunion := (measure_iUnion_le E).trans Hsum
  refine ⟨hE, MeasurableSet.iUnion hE, Hsum, Hunion,
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top Hunion, ?_⟩
  intro j θ ζ hθ hζ ρ hρ hn
  exact (Hdata j).2.2.2 θ ζ hθ hζ ρ hρ (fun hbad => hn (mem_iUnion_of_mem j hbad))

end BianchiIX
