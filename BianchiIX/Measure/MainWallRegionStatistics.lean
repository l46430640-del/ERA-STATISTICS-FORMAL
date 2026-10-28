import BianchiIX.Measure.AngularRegionStatistics
import BianchiIX.Measure.ShearRegionStatistics
import BianchiIX.Statistics.EraCapMonotonicity

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal

def mainWallSmallSection (d : ℝ) : Set SectionCoordinates :=
  {z | |z 0| ≤ d ∧ max (Real.exp (-z 1)) (Real.exp (-z 2)) ≤ d}

theorem measurableSet_mainWallSmallSection (d : ℝ) : MeasurableSet (mainWallSmallSection d) := by
  have hs : Measurable (fun z : SectionCoordinates => |z 0|) := by fun_prop
  have hm : Measurable (fun z : SectionCoordinates => max (Real.exp (-z 1)) (Real.exp (-z 2))) := by fun_prop
  exact (measurableSet_le hs measurable_const).inter (measurableSet_le hm measurable_const)

/-- The angular and shear regions cover every small positive-wall section point, including zero shear. -/
theorem mainWallSmallSection_subset_regions (d : ℝ) :
    mainWallSmallSection d ⊆ angularSection d 128 ∪ shearSection d (1 / 128) := by
  intro z hz
  by_cases hs : |z 0| ≤ 128 * max (Real.exp (-z 1)) (Real.exp (-z 2))
  · exact Or.inl ⟨hz.2, hs⟩
  · have hm : 0 < max (Real.exp (-z 1)) (Real.exp (-z 2)) := lt_max_of_lt_left (Real.exp_pos _)
    have H := lt_of_not_ge hs
    have hweak : max (Real.exp (-z 1)) (Real.exp (-z 2)) ≤ 1 / 128 * |z 0| := by linarith only [H]
    exact Or.inr ⟨⟨by linarith only [H, hm], hz.1⟩,
      (le_max_left _ _).trans hweak, (le_max_right _ _).trans hweak⟩

/-- One finite-flux Borel exception set covers the entire small main-wall section and yields an exact statistical future. -/
theorem exists_mainWallRegion_statistics (hBirkhoff : Literature.BirkhoffErgodicInput ℝ) :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 20 ≤ J → ∀ σ : ℝ, 0 < σ → σ < 1 → σ * (2 * J : ℕ) < 1 →
        ∃ Bcap > (0 : ℝ), Bcap < 1 ∧ ∃ hstar > (0 : ℝ),
          ∀ h ∈ Ioc (0 : ℝ) hstar, ∀ q D P : ℝ, 3 < q → 4 < D → 6 * D + 2 < P →
            ∃ dstar > (0 : ℝ), ∃ C > (0 : ℝ), ∀ d ∈ Ioc (0 : ℝ) dstar,
              ∃ F : Set SectionCoordinates, MeasurableSet F ∧
                mainWallMeasure h F ≤ ENNReal.ofReal (C * d * (1 + |Real.log d|) ^ 2) ∧
                mainWallMeasure h F ≠ ⊤ ∧
                ∀ z ∈ mainWallSmallSection d \ F,
                  z ∈ mainWallChartDomain h ∧ StatisticalCoreFuture η J σ Bcap (mainWallChart h z) := by
  obtain ⟨δA, hδA, hδmax, HδA⟩ := exists_angularRegion_statistics hBirkhoff
  obtain ⟨δS, hδS, _, HδS⟩ := exists_shearRegion_statistics hBirkhoff
  refine ⟨min δA δS, lt_min hδA hδS, (min_le_left _ _).trans hδmax, ?_⟩
  intro η hη hηδ J hJ σ hσ hσone hσJ
  obtain ⟨BA, hBA, hBAone, hA, hhA, HA⟩ :=
    HδA η hη (hηδ.trans (min_le_left _ _)) J hJ σ hσ hσone hσJ
  obtain ⟨BS, hBS, hBSone, hS, hhS, HS⟩ :=
    HδS η hη (hηδ.trans (min_le_right _ _)) J hJ σ hσ hσone hσJ
  refine ⟨max BA BS, hBA.trans_le (le_max_left _ _), max_lt hBAone hBSone,
    min hA hS, lt_min hhA hhS, ?_⟩
  intro h hh q D P hq hD hP
  have hPpos : 0 < P := by linarith only [hD, hP]
  obtain ⟨dA, hdA, HdA⟩ := HA h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ 128 (by norm_num)
    q P hq (by linarith only [hD, hP])
  obtain ⟨dS, hdS, HdS⟩ := HS h ⟨hh.1, hh.2.trans (min_le_right _ _)⟩ q D P hq hD hP
  let KA := 12 * 128 * logarithmicFluxConstantOne (angularFailureFluxConstant 128 σ) σ + 24 * 128 * P * Real.log 2
  let KS := 66 * logarithmicFluxConstant (shearFailureFluxConstant σ) σ + 132 * P ^ 2
  have hlog : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  have hKA : 0 ≤ KA := add_nonneg
    (mul_nonneg (by norm_num) (logarithmicFluxConstantOne_nonneg (angularFailureFluxConstant_ge_one (by norm_num) hσ.le) hσ))
    (by positivity)
  have hKS : 0 < KS := add_pos_of_nonneg_of_pos
    (mul_nonneg (by norm_num) (logarithmicFluxConstant_nonneg (shearFailureFluxConstant_ge_one hσ.le) hσ))
    (mul_pos (by norm_num) (sq_pos_of_pos hPpos))
  refine ⟨min dA dS, lt_min hdA hdS, 3 * KA + KS,
    add_pos_of_nonneg_of_pos (mul_nonneg (by norm_num) hKA) hKS, ?_⟩
  intro d hd
  let FA := angularFailureRegion h q d 128 P η J σ BA
  let FS := shearFailureRegion h q d (1 / 128) P η J σ BS
  obtain ⟨hFA, HAbound, _, HAgood⟩ := HdA d ⟨hd.1, hd.2.trans (min_le_left _ _)⟩
  obtain ⟨hFS, HSbound, _, HSgood⟩ := HdS d ⟨hd.1, hd.2.trans (min_le_right _ _)⟩ (1 / 128) (by norm_num)
  have hW : 1 + |Real.log d| + 2 * Real.log 2 ≤ 3 * (1 + |Real.log d|) ^ 2 := by
    have hlog2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    nlinarith only [hlog2, abs_nonneg (Real.log d), sq_nonneg (Real.log d)]
  have HA' : mainWallMeasure h FA ≤ ENNReal.ofReal (3 * KA * d * (1 + |Real.log d|) ^ 2) :=
    HAbound.trans (ENNReal.ofReal_le_ofReal
      ((mul_le_mul_of_nonneg_left hW (mul_nonneg hKA hd.1.le)).trans_eq (by ring)))
  have Hbound : mainWallMeasure h (FA ∪ FS) ≤
      ENNReal.ofReal ((3 * KA + KS) * d * (1 + |Real.log d|) ^ 2) := calc
    _ ≤ _ := measure_union_le FA FS
    _ ≤ ENNReal.ofReal (3 * KA * d * (1 + |Real.log d|) ^ 2) +
        ENNReal.ofReal (KS * d * (1 + |Real.log d|) ^ 2) := add_le_add HA' HSbound
    _ = _ := by
      rw [← ENNReal.ofReal_add
        (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) hKA) hd.1.le)
          (sq_nonneg (1 + |Real.log d|)))
        (mul_nonneg (mul_nonneg hKS.le hd.1.le) (sq_nonneg (1 + |Real.log d|)))]
      congr 1
      ring
  refine ⟨FA ∪ FS, hFA.union hFS, Hbound, ne_top_of_le_ne_top ENNReal.ofReal_ne_top Hbound, ?_⟩
  intro z hz
  rcases mainWallSmallSection_subset_regions d hz.1 with hangle | hshear
  · obtain ⟨hy, H⟩ := HAgood z ⟨hangle, fun hbad => hz.2 (Or.inl hbad)⟩
    exact ⟨hy, H.mono_cap (le_max_left _ _)⟩
  · obtain ⟨hy, H⟩ := HSgood z ⟨hshear, fun hbad => hz.2 (Or.inr hbad)⟩
    exact ⟨hy, H.mono_cap (le_max_right _ _)⟩

end BianchiIX
