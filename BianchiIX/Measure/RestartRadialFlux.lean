import BianchiIX.Measure.RadialFailureComparison

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal

/-- The fixed disjoint statistical failure set has both its exact flux integral and the quantitative finite-flux bound. -/
theorem exists_restartRadialFailure_quantitative (hBirkhoff : Literature.BirkhoffErgodicInput ℝ) :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 20 ≤ J → ∀ σ : ℝ, 0 < σ → σ < 1 → σ * (2 * J : ℕ) < 1 →
        ∃ Bcap > (0 : ℝ), Bcap < 1 ∧ ∃ hstar > (0 : ℝ), hstar ≤ 1 / 8 ∧
          ∀ h ∈ Ioc (0 : ℝ) hstar, ∀ q D P : ℝ, 3 < q → 4 < D → 6 * D + 2 < P →
            ∀ ε ∈ Ioc (0 : ℝ) (1 / 128), ∃ C > (0 : ℝ),
              ∃ dstar > (0 : ℝ), dstar ≤ h / 8 ∧ ∀ d ∈ Ioc (0 : ℝ) dstar,
                let F := restartRadialFailureFamily h q d ε P η J σ Bcap
                let E := radialFailureSet d ε F
                (∀ i, MeasurableSet (F i)) ∧ MeasurableSet E ∧
                  mainWallOriginalMeasure h E = (∑' i, radialFailureIntegral h d ε F i) ∧
                  mainWallOriginalMeasure h E ≤ ENNReal.ofReal (C * d * (1 + |Real.log d|) ^ 2) ∧
                  mainWallOriginalMeasure h E ≠ ⊤ ∧
                  (∀ z ∈ mainWallOpenSection d \ E,
                    ∃ i : RadialPieceIndex, z ∈ physicalRadialPiece d ε i ∧
                      restartRadialOutput h q d ε i (radialPieceInverse i.1 z) ∈
                        EraSurvivor.typicalDomain η J σ Bcap) ∧
                  ∀ i z, z ∈ radialPieceDomain d ε i → z ∉ F i →
                    ∃ p : eraSurvivorDomain η J σ Bcap,
                      p.val = restartRadialOutput h q d ε i z ∧
                      EraStatistics (EraSurvivor.digits p) (EraSurvivor.phase p) := by
  obtain ⟨δG, hδG, hδmax, HG⟩ := exists_restartRadialFailure_partition hBirkhoff
  obtain ⟨δA, hδA, _, HA⟩ := exists_angularRegion_statistics hBirkhoff
  obtain ⟨δS, hδS, _, HS⟩ := exists_shearRegion_statistics hBirkhoff
  refine ⟨min δG (min δA δS), lt_min hδG (lt_min hδA hδS), (min_le_left _ _).trans hδmax, ?_⟩
  intro η hη hηδ J hJ σ hσ hσ1 hσJ
  obtain ⟨Bcap, hcap, hcap1, hG, hhG, hhG1, HG⟩ :=
    HG η hη (hηδ.trans (min_le_left _ _)) J hJ σ hσ hσ1 hσJ
  obtain ⟨BA, _, _, hA, hhA, HA⟩ :=
    HA η hη (hηδ.trans ((min_le_right _ _).trans (min_le_left _ _))) J hJ σ hσ hσ1 hσJ
  obtain ⟨BS, _, _, hS, hhS, HS⟩ :=
    HS η hη (hηδ.trans ((min_le_right _ _).trans (min_le_right _ _))) J hJ σ hσ hσ1 hσJ
  refine ⟨Bcap, hcap, hcap1, min hG (min hA hS), lt_min hhG (lt_min hhA hhS),
    (min_le_left _ _).trans hhG1, ?_⟩
  intro h hh q D P hq hD hP ε hε
  let L := 1 / ε
  have hL : 0 ≤ L := by dsimp only [L]; positivity [hε.1]
  let CA := 12 * L * logarithmicFluxConstantOne (angularFailureFluxConstant L σ) σ + 24 * L * P * Real.log 2
  let CS := 66 * logarithmicFluxConstant (shearFailureFluxConstant σ) σ + 132 * P ^ 2
  have hPpos : 0 < P := by linarith only [hD, hP]
  have hlog : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  have hCA : 0 ≤ CA := add_nonneg
    (mul_nonneg (mul_nonneg (by norm_num) hL)
      (logarithmicFluxConstantOne_nonneg (angularFailureFluxConstant_ge_one hL hσ.le) hσ)) (by positivity)
  have hCS : 0 < CS := add_pos_of_nonneg_of_pos
    (mul_nonneg (by norm_num) (logarithmicFluxConstant_nonneg (shearFailureFluxConstant_ge_one hσ.le) hσ))
    (mul_pos (by norm_num) (sq_pos_of_pos hPpos))
  have hw : 0 < 1 + 4 * h ^ 2 := by positivity
  refine ⟨(1 + 4 * h ^ 2) * (3 * CA + CS),
    mul_pos hw (add_pos_of_nonneg_of_pos (by positivity) hCS), ?_⟩
  obtain ⟨dG, hdG, hdGh, HDG⟩ := HG h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q D P hq hD hP ε hε
  obtain ⟨dA, hdA, HDA⟩ := HA h ⟨hh.1, hh.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩
    L hL q P hq (by linarith only [hD, hP])
  obtain ⟨dS, hdS, HDS⟩ := HS h ⟨hh.1, hh.2.trans ((min_le_right _ _).trans (min_le_right _ _))⟩ q D P hq hD hP
  let K := 51200 * (L + 1)
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨min dG (min dA (min dS (min 1 (min (Bcap / 800) (Bcap / K))))),
    lt_min hdG (lt_min hdA (lt_min hdS (lt_min zero_lt_one
      (lt_min (div_pos hcap (by norm_num)) (div_pos hcap hK))))),
    (min_le_left _ _).trans hdGh, ?_⟩
  intro d hd F E
  have hd' := hd.2.trans (min_le_right _ _)
  have hd'' := hd'.trans (min_le_right _ _)
  have hd''' := hd''.trans (min_le_right _ _)
  have hdnum := hd'''.trans (min_le_right _ _)
  have hdG' : d ≤ dG := hd.2.trans (min_le_left _ _)
  have hd1 : d ≤ 1 := hd'''.trans (min_le_left _ _)
  have hdh : d ≤ h := by linarith only [hdG'.trans hdGh, hh.1]
  have hSd : 800 * d ≤ Bcap := by
    have H := (le_div_iff₀ (by norm_num : (0 : ℝ) < 800)).mp (hdnum.trans (min_le_left _ _))
    nlinarith only [H]
  have hAd : K * d ≤ Bcap := by
    have H := (le_div_iff₀ hK).mp (hdnum.trans (min_le_right _ _))
    nlinarith only [H]
  obtain ⟨hF, hE, Heq, Hgood, Hstats⟩ := HDG d ⟨hd.1, hdG'⟩
  obtain ⟨_, HAbound, _, _⟩ := HDA d ⟨hd.1, hd'.trans (min_le_left _ _)⟩
  obtain ⟨_, HSbound, _, _⟩ := HDS d ⟨hd.1, hd''.trans (min_le_left _ _)⟩ ε ⟨hε.1.le, hε.2⟩
  have Hregions := mainWallOriginalMeasure_radialFailure_le_regions (BA := BA) (BS := BS)
    hh.1 hd.1 hd1 hdh ⟨hε.1.le, hε.2⟩ hL (by linarith only [hD, hP]) hcap1.le hSd hAd hE
  have hweight : 1 + |Real.log d| + 2 * Real.log 2 ≤ 3 * (1 + |Real.log d|) ^ 2 := by
    have hlog2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    nlinarith only [hlog2, abs_nonneg (Real.log d), sq_nonneg (Real.log d)]
  have HA' : mainWallMeasure h (angularFailureRegion h q d L P η J σ BA) ≤
      ENNReal.ofReal (3 * CA * d * (1 + |Real.log d|) ^ 2) :=
    HAbound.trans (ENNReal.ofReal_le_ofReal
      ((mul_le_mul_of_nonneg_left hweight (mul_nonneg hCA hd.1.le)).trans_eq (by ring)))
  have Hbound : mainWallOriginalMeasure h E ≤
      ENNReal.ofReal ((1 + 4 * h ^ 2) * (3 * CA + CS) * d * (1 + |Real.log d|) ^ 2) := calc
    _ ≤ _ := Hregions
    _ ≤ ENNReal.ofReal (1 + 4 * h ^ 2) *
        (ENNReal.ofReal (3 * CA * d * (1 + |Real.log d|) ^ 2) +
          ENNReal.ofReal (CS * d * (1 + |Real.log d|) ^ 2)) := mul_le_mul' le_rfl (add_le_add HA' HSbound)
    _ = _ := by
      rw [← ENNReal.ofReal_add
        (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCA) hd.1.le) (sq_nonneg _))
        (mul_nonneg (mul_nonneg hCS.le hd.1.le) (sq_nonneg _)), ← ENNReal.ofReal_mul hw.le]
      congr 1
      ring
  exact ⟨hF, hE, Heq, Hbound, ne_top_of_le_ne_top ENNReal.ofReal_ne_top Hbound, Hgood, Hstats⟩

end BianchiIX
