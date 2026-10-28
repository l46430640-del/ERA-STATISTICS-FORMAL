import BianchiIX.Measure.ShearFailureLayer

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal

/-- The selected positive-shear statistical failures have a summable corrected-flux budget across all dyadic scales. -/
theorem exists_restartShear_failure_dyadic_flux (hBirkhoff : Literature.BirkhoffErgodicInput ℝ) :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 20 ≤ J → ∀ σ : ℝ, 0 < σ → σ < 1 → σ * (2 * J : ℕ) < 1 →
        ∃ Bcap > (0 : ℝ), Bcap < 1 ∧ ∃ hstar > (0 : ℝ),
          ∀ h ∈ Ioc (0 : ℝ) hstar, ∀ q P : ℝ, 3 < q → 4 < P → ∃ dstar > (0 : ℝ),
            ∀ d ∈ Ioc (0 : ℝ) dstar, ∀ ε : ℝ, (0 ≤ ε ∧ ε ≤ 1 / 64) →
              let L := fun j => restartShearFailureLayer h
                (q / 2 * Real.log (1 / dyadicScale d j)) (dyadicScale d j) ε P η J σ Bcap
              (∑' j, L j) ≤ ENNReal.ofReal
                (33 * logarithmicFluxConstant (shearFailureFluxConstant σ) σ * d * (1 + |Real.log d|) ^ 2) ∧
                (∑' j, L j) ≠ ⊤ := by
  obtain ⟨δ, hδ, hδmax, Hδ⟩ := exists_restartShear_failure_layer hBirkhoff
  refine ⟨δ, hδ, hδmax, ?_⟩
  intro η hη hηδ J hJ σ hσ hσone hσJ
  obtain ⟨Bcap, hcap, hcapone, hstar, hhstar, HH⟩ := Hδ η hη hηδ J hJ σ hσ hσone hσJ
  refine ⟨Bcap, hcap, hcapone, hstar, hhstar, ?_⟩
  intro h hh q P hq hP
  obtain ⟨astar, hastar, Ha⟩ := HH h hh q P hq hP
  refine ⟨min astar 1, lt_min hastar zero_lt_one, ?_⟩
  intro d hd ε hε L
  let K := 3 * logarithmicFluxConstant (shearFailureFluxConstant σ) σ
  have hK : 0 ≤ K := mul_nonneg (by norm_num)
    (logarithmicFluxConstant_nonneg (shearFailureFluxConstant_ge_one hσ.le) hσ)
  have Hlayer (j : ℕ) : L j ≤ ENNReal.ofReal
      (K * (dyadicScale d j * (1 + |Real.log (dyadicScale d j)|) ^ 2)) := by
    have H := (Ha (dyadicScale d j)
      ⟨dyadicScale_pos hd.1 j, (dyadicScale_le hd.1.le j).trans (hd.2.trans (min_le_left _ _))⟩ ε hε).1
    simpa only [L, K, mul_assoc] using H
  have Hfinal : (∑' j, L j) ≤ ENNReal.ofReal
      (33 * logarithmicFluxConstant (shearFailureFluxConstant σ) σ * d * (1 + |Real.log d|) ^ 2) := calc
    _ ≤ _ := ENNReal.tsum_le_tsum Hlayer
    _ ≤ _ := dyadic_flux_budget hd.1 (hd.2.trans (min_le_right _ _)) hK
    _ = _ := by congr 1; dsimp only [K]; ring
  exact ⟨Hfinal, ne_top_of_le_ne_top ENNReal.ofReal_ne_top Hfinal⟩

end BianchiIX
