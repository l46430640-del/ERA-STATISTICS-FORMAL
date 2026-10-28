import BianchiIX.Statistics.EraCodingRealization

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal

/-- One Borel set of actual states supplies the same statistical set and loss bound on every admissible curve. -/
theorem exists_era_joint_statistics (hBirkhoff : Literature.BirkhoffErgodicInput ℝ) :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 20 ≤ J → ∀ σ : ℝ, 0 < σ → σ < 1 → σ * (2 * J : ℕ) < 1 →
        ∃ Bcap > (0 : ℝ), Bcap < 1 ∧ MeasurableSet (EraSurvivor.typicalDomain η J σ Bcap) ∧
          ∃ Bstar > (0 : ℝ), Bstar ≤ Bcap ∧ ∀ B ∈ Ioc 0 Bstar,
            ∀ Γ : EraCurve, Γ.Admissible B →
              MeasurableSet (EraSurvivor.curveTypicalSet Γ η J σ B Bcap) ∧
              (1 / 2 : ℝ≥0∞) < volume (EraSurvivor.curveTypicalSet Γ η J σ B Bcap) ∧
              (∀ I : Set ℝ, volume ((I ∩ Ioo 0 1) \ (I ∩ EraSurvivor.curveTypicalSet Γ η J σ B Bcap)) ≤
                min (volume I) (ENNReal.ofReal (80 * B ^ σ))) ∧
              ∀ x ∈ EraSurvivor.curveTypicalSet Γ η J σ B Bcap,
                ∃ p : eraSurvivorDomain η J σ Bcap, p.val = (B, Γ.state (2 / x)) ∧
                  EraStatistics (EraSurvivor.digits p) (EraSurvivor.phase p) := by
  obtain ⟨δt, hδt, hδmax, HT⟩ := exists_era_curve_family
  obtain ⟨δs, hδs, _, HS⟩ := exists_era_selected_return
  refine ⟨min δt δs, lt_min hδt hδs, (min_le_left _ _).trans hδmax, ?_⟩
  intro η hη hηδ J hJ σ hσ hσone hσJ
  obtain ⟨C, hC, Bt, hBt, hBtone, Htree⟩ := HT η hη (hηδ.trans (min_le_left _ _)) J hJ σ hσ hσone hσJ
  obtain ⟨Bs, hBs, hBsone, Hmeas, Hselect⟩ := HS η hη (hηδ.trans (min_le_right _ _)) J hJ σ hσ hσone hσJ
  have hC0 : 0 ≤ C := by linarith
  have hCi : 0 ≤ 5 * C := mul_nonneg (by norm_num) hC0
  obtain ⟨Bb, hBb, _, Hbudget⟩ :=
    exists_era_budget_threshold hσ hC0 hCi (show (0 : ℝ) ≤ 0 by rfl)
  refine ⟨Bs, hBs, hBsone, EraSurvivor.typicalDomain_measurable Hmeas,
    min Bt (min Bs Bb), lt_min hBt (lt_min hBs hBb), (min_le_right _ _).trans (min_le_left _ _), ?_⟩
  intro B hB Γ hΓ
  have hBt' : B ∈ Ioc 0 Bt := ⟨hB.1, hB.2.trans (min_le_left _ _)⟩
  have hBs' : B ∈ Ioc 0 Bs := ⟨hB.1, hB.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩
  have hBb' : B ∈ Ioc 0 Bb := ⟨hB.1, hB.2.trans ((min_le_right _ _).trans (min_le_right _ _))⟩
  have Hnodes := Htree B hBt' Γ hΓ
  let T := Γ.inverseTree η J σ B C (fun w => (Hnodes w).2)
  have R : Γ.Realization η J σ B Bs T := EraCurve.realization_of_estimates hBs' hBsone.le Hnodes Hselect
  have E := EraCurve.inverseTree_estimates hB.1 hC0 (fun w => (Hnodes w).2)
  obtain ⟨hsmall, hL, _⟩ := Hbudget B hBb'
  have hJreal : (2 : ℝ) ≤ (2 * J : ℕ) := by exact_mod_cast (show 2 ≤ 2 * J by omega)
  have hσhalf : σ ≤ 1 / 2 := by nlinarith
  have Hstats := E.typicalSurvivors_era_bounds hBirkhoff R.root hB.1 (hBs'.2.trans hBsone.le)
    hσ.le hσhalf hsmall hC0 hCi hL (EraCurve.inverseTree_stopped_volume hB.1 hC0 (fun w => (Hnodes w).2))
  have heq := R.curveTypicalSet_eq
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [heq]
    exact T.typicalSurvivors_measurable
  · rw [heq]
    exact Hstats.1
  · intro I
    rw [heq, ← R.root]
    exact Hstats.2.1 I
  · intro x hx
    have ht : x ∈ T.typicalSurvivors := by rwa [← heq]
    let xt : T.survivors := ⟨x, T.typicalSurvivors_subset ht⟩
    let p : eraSurvivorDomain η J σ Bs :=
      ⟨(B, Γ.state (2 / x)), (R.survivor_iff x (T.survivors_subset_root xt.property)).mpr xt.property⟩
    refine ⟨p, rfl, ?_⟩
    rw [R.digits_eq_tree xt p rfl, R.phase_eq_tree xt p rfl]
    exact Hstats.2.2 xt ht

end BianchiIX
