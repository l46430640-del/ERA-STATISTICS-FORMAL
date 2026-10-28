import BianchiIX.Measure.AngularFailureOrders

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal

/-- A single Borel exceptional set of finite flux covers all scales and both weak-wall orderings. -/
theorem exists_restartAngular_two_orders_dyadic (hBirkhoff : Literature.BirkhoffErgodicInput ℝ) :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 20 ≤ J → ∀ σ : ℝ, 0 < σ → σ < 1 → σ * (2 * J : ℕ) < 1 →
        ∃ Bcap > (0 : ℝ), Bcap < 1 ∧ ∃ hstar > (0 : ℝ),
          ∀ h ∈ Ioc (0 : ℝ) hstar, ∀ L : ℝ, 0 ≤ L →
            ∀ q P : ℝ, 3 < q → 4 < P → ∃ dstar > (0 : ℝ),
              ∀ d ∈ Ioc (0 : ℝ) dstar,
                let E := fun j => mainWallSymmetrization (restartAngularFailureSection h
                  (q / 2 * Real.log (1 / dyadicScale d j)) (dyadicScale d j) L P η J σ Bcap)
                let K := 12 * L * logarithmicFluxConstantOne (angularFailureFluxConstant L σ) σ
                (∀ j : ℕ, MeasurableSet (E j)) ∧ MeasurableSet (⋃ j : ℕ, E j) ∧
                  (∑' j : ℕ, mainWallMeasure h (E j)) ≤ ENNReal.ofReal (K * d * (1 + |Real.log d| + 2 * Real.log 2)) ∧
                  mainWallMeasure h (⋃ j : ℕ, E j) ≤ ENNReal.ofReal (K * d * (1 + |Real.log d| + 2 * Real.log 2)) ∧
                  mainWallMeasure h (⋃ j : ℕ, E j) ≠ ⊤ ∧
                  ∀ j : ℕ, ∀ θ ζ : ℝ, |θ| ≤ L → (0 < ζ ∧ ζ ≤ (dyadicScale d j) ^ P) →
                    ∀ ρ ∈ Icc (dyadicScale d j) (2 * dyadicScale d j),
                      let s := q / 2 * Real.log (1 / dyadicScale d j)
                      let y : SectionCoordinates := ![θ * ρ, -Real.log ρ, -Real.log ζ]
                      let T := restartReturnTime h s θ ζ ρ
                      y ∈ mainWallChartDomain h ∧ 0 < T ∧ T ∈ normalizedMaxDomain (mainWallChart h y) 0 ∧
                        ((y ∉ ⋃ i : ℕ, E i ∨ mainWallReflection y ∉ ⋃ i : ℕ, E i) →
                        ∃ p : eraSurvivorDomain η J σ Bcap,
                          p.val = (restartAmplitudeBudget L (dyadicScale d j) ζ, restartReturnState h s θ ζ ρ) ∧
                          EraStatistics (EraSurvivor.digits p) (EraSurvivor.phase p) ∧
                          coreRadiusEntry p.val.2 = projectiveReflection (toProjectiveState
                            (normalizedMaxCurve (mainWallChart h y) 0 T)) ∧
                          coreRadiusEntry p.val.2 = toProjectiveState
                            (normalizedMaxCurve (mainWallChart h (mainWallReflection y)) 0 T)) := by
  obtain ⟨δ, hδ, hδmax, Hδ⟩ := exists_restartAngular_two_orders hBirkhoff
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
  intro j θ ζ hθ hζ ρ hρ s y T
  obtain ⟨hy, ht, hdom, Hgood⟩ := (Hdata j).2.2.2 θ ζ hθ hζ ρ hρ
  refine ⟨hy, ht, hdom, ?_⟩
  intro H
  apply Hgood
  exact H.imp (fun hn hbad => hn (mem_iUnion_of_mem j hbad))
    (fun hn hbad => hn (mem_iUnion_of_mem j hbad))

end BianchiIX
