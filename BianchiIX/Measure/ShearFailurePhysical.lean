import BianchiIX.Measure.ShearFailureTonelli

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal

/-- The actual positive-shear annulus has a Borel physical failure set, finite flux, and statistics at every selected point outside it. -/
theorem exists_restartShear_physical_failure (hBirkhoff : Literature.BirkhoffErgodicInput ℝ) :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 20 ≤ J → ∀ σ : ℝ, 0 < σ → σ < 1 → σ * (2 * J : ℕ) < 1 →
        ∃ Bcap > (0 : ℝ), Bcap < 1 ∧ ∃ hstar > (0 : ℝ),
          ∀ h ∈ Ioc (0 : ℝ) hstar, ∀ q P : ℝ, 3 < q → 4 < P → ∃ astar > (0 : ℝ),
            ∀ a ∈ Ioc (0 : ℝ) astar, ∀ ε : ℝ, (0 ≤ ε ∧ ε ≤ 1 / 64) →
              let s := q / 2 * Real.log (1 / a)
              let E := restartShearFailureSection h s a ε P η J σ Bcap
              let K := 3 * logarithmicFluxConstant (shearFailureFluxConstant σ) σ
              MeasurableSet E ∧ mainWallMeasure h E = restartShearFailureLayer h s a ε P η J σ Bcap ∧
                mainWallMeasure h E ≤ ENNReal.ofReal (K * a * (1 + |Real.log a|) ^ 2) ∧
                mainWallMeasure h E ≠ ⊤ ∧
                ∀ n₂ n₃ : ℝ, (n₂, n₃) ∈ restartShearLabelSet ε a P →
                  ∀ ρ ∈ Icc a (2 * a), ![ρ, -Real.log n₂, -Real.log n₃] ∉ E →
                    ∃ p : eraSurvivorDomain η J σ Bcap,
                      p.val = (restartShearAmplitudeBudget a n₂ n₃, restartShearReturnState h s n₂ n₃ ρ) ∧
                      EraStatistics (EraSurvivor.digits p) (EraSurvivor.phase p) := by
  obtain ⟨δ, hδ, hδmax, Hδ⟩ := exists_restartShear_era_statistics hBirkhoff
  refine ⟨δ, hδ, hδmax, ?_⟩
  intro η hη hηδ J hJ σ hσ hσone hσJ
  obtain ⟨Bcap, hcap, hcapone, hS, hhS, HS⟩ := Hδ η hη hηδ J hJ σ hσ hσone hσJ
  refine ⟨Bcap, hcap, hcapone, min hS (1 / 8), lt_min hhS (by norm_num), ?_⟩
  intro h hh q P hq hP
  have hh1 : h ≤ 1 / 8 := hh.2.trans (min_le_right _ _)
  obtain ⟨aS, haS, HaS⟩ := HS h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q P hq hP
  refine ⟨min aS (min (h / 8) 1), lt_min haS (lt_min (div_pos hh.1 (by norm_num)) zero_lt_one), ?_⟩
  intro a ha ε hε s E K
  have hah : a ≤ h / 8 := ha.2.trans ((min_le_right _ _).trans (min_le_left _ _))
  have ha1 : a ≤ 1 := ha.2.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨hjoint, Hstats⟩ := HaS a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε hε
  have hA := measurableSet_restartShearFailureCoordinates hjoint
  have heq := mainWallMeasure_restartShearFailureSection hh.1 hh1 ha.1 hah hε hA
  have Hslice (n₂ n₃ : ℝ) (hl : (n₂, n₃) ∈ restartShearLabelSet ε a P) :
      restartShearRadialFlux h n₂ n₃
        (eraRadialFailure η J σ (restartShearAmplitudeBudget a n₂ n₃) Bcap a (2 * a)
          (restartShearReturnState h s n₂ n₃)) ≤
        ENNReal.ofReal (3 * min a (640 * Real.sqrt 3 * (restartShearAmplitudeBudget a n₂ n₃) ^ σ)) := by
    let F := eraRadialFailure η J σ (restartShearAmplitudeBudget a n₂ n₃) Bcap a (2 * a)
      (restartShearReturnState h s n₂ n₃)
    have hFI : F ⊆ Icc a (2 * a) := fun _ hρ => hρ.1
    obtain ⟨_, hF, Hloss, _⟩ := Hstats n₂ n₃ hl.1 hl.2.1 hl.2.2
    have H := (Hloss F hF hFI (fun ρ => ENNReal.ofReal (restartShearFluxDensity h n₂ n₃ ρ))
      3 (by norm_num) (fun ρ hρ => ENNReal.ofReal_le_ofReal
        (restartShearFluxDensity_bounds hh.1 hh1 ha.1 hah hε
          ⟨hl.1.1.le, hl.1.2⟩ ⟨hl.2.1.1.le, hl.2.1.2⟩ (hFI hρ)).2)).trans (min_le_right _ _)
    change (∫⁻ ρ in F ∩ F, _) ≤ _ at H
    rw [inter_self] at H
    by_cases hm : a ≤ 640 * Real.sqrt 3 * (restartShearAmplitudeBudget a n₂ n₃) ^ σ
    · rw [min_eq_left hm]
      exact restartShearRadialFlux_le hh.1 hh1 ha.1 hah hε
        ⟨hl.1.1.le, hl.1.2⟩ ⟨hl.2.1.1.le, hl.2.1.2⟩ hFI
    · rw [min_eq_right (le_of_not_ge hm)]
      exact H.trans_eq (by congr 1; ring)
  have Hbound : mainWallMeasure h E ≤ ENNReal.ofReal (K * a * (1 + |Real.log a|) ^ 2) := calc
    _ = _ := heq
    _ ≤ _ := restartShearFailureLayer_le ha.1 Hslice
    _ ≤ 3 * ENNReal.ofReal (logarithmicFluxConstant (shearFailureFluxConstant σ) σ * a * (1 + |Real.log a|) ^ 2) :=
      mul_le_mul' le_rfl (logarithmicLayerCost_le ha.1 ha1 (shearFailureFluxConstant_ge_one hσ.le) hσ)
    _ = _ := by
      rw [show (3 : ℝ≥0∞) = ENNReal.ofReal (3 : ℝ) by norm_num, ← ENNReal.ofReal_mul (by norm_num)]
      congr 1
      dsimp only [K]
      ring
  refine ⟨measurableSet_restartShearFailureSection ha.1 hA, heq, Hbound,
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top Hbound, ?_⟩
  intro n₂ n₃ hl ρ hρ hn
  exact (Hstats n₂ n₃ hl.1 hl.2.1 hl.2.2).2.2.2 ρ hρ
    (fun hbad => hn ((mem_restartShearFailureSection_iff ha.1 hε.2 hl).mpr hbad))

end BianchiIX
