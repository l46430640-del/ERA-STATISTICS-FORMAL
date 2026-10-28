import BianchiIX.Statistics.EraInverseTree
import BianchiIX.Statistics.EraBudget

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal

/-- A common measurable statistical set for the tree of exact era maps on an admissible curve. -/
theorem exists_era_curve_statistics (hBirkhoff : Literature.BirkhoffErgodicInput ℝ) :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 20 ≤ J → ∀ σ : ℝ, 0 < σ → σ < 1 → σ * (2 * J : ℕ) < 1 →
        ∃ Bstar > (0 : ℝ), Bstar < 1 ∧
          ∀ B ∈ Ioc 0 Bstar, ∀ Γ : EraCurve, Γ.Admissible B →
            ∃ T : InverseBranchTree, T.root = Ioo 0 1 ∧
              T.branch = Γ.treeBranch η J σ B ∧ T.domain = eraTreeDomain σ B ∧
              (∀ x : T.survivors, ∀ n : ℕ,
                let X := (Γ.family η J σ B (T.word x n)).state (2 / T.phase x n)
                eraOutputRadius η J (T.digits x n).natPred X = 2 / T.phase x (n + 1) ∧
                  (Γ.family η J σ B (T.word x (n + 1))).U (2 / T.phase x (n + 1)) =
                    eraOutputState η J (T.digits x n).natPred X 1 ∧
                  (Γ.family η J σ B (T.word x (n + 1))).W (2 / T.phase x (n + 1)) =
                    eraOutputState η J (T.digits x n).natPred X 3) ∧
              ∃ G : Set ℝ, MeasurableSet G ∧ G ⊆ T.survivors ∧ (1 / 2 : ℝ≥0∞) < volume G ∧
                (∀ I : Set ℝ, volume ((I ∩ Ioo 0 1) \ (I ∩ G)) ≤
                  min (volume I) (ENNReal.ofReal (80 * B ^ σ))) ∧
                ∀ x : T.survivors, x.val ∈ G → EraStatistics (T.digits x) (T.phase x) := by
  obtain ⟨δ, hδ, hδmax, Hδ⟩ := exists_era_inverse_tree
  refine ⟨δ, hδ, hδmax, ?_⟩
  intro η hη hηδ J hJ σ hσ hσone hσJ
  obtain ⟨C, hC, Bt, hBt, hBtone, Ht⟩ := Hδ η hη hηδ J hJ σ hσ hσone hσJ
  have hC0 : 0 ≤ C := by linarith
  have hCi : 0 ≤ 5 * C := mul_nonneg (by norm_num) hC0
  obtain ⟨Bb, hBb, hBbone, Hb⟩ :=
    exists_era_budget_threshold hσ hC0 hCi (show (0 : ℝ) ≤ 0 by rfl)
  refine ⟨min Bt Bb, lt_min hBt hBb, (min_le_left _ _).trans_lt hBtone, ?_⟩
  intro B hB Γ hΓ
  have hB1 : B ≤ 1 := (hB.2.trans (min_le_left _ _)).trans hBtone.le
  obtain ⟨T, hroot, hbranch, hdomain, E, hsize, hmatch⟩ :=
    Ht B ⟨hB.1, hB.2.trans (min_le_left _ _)⟩ Γ hΓ
  obtain ⟨hsmall, hL, _⟩ := Hb B ⟨hB.1, hB.2.trans (min_le_right _ _)⟩
  have hJreal : (2 : ℝ) ≤ (2 * J : ℕ) := by exact_mod_cast (show 2 ≤ 2 * J by omega)
  have hσhalf : σ ≤ 1 / 2 := by nlinarith
  obtain ⟨G, hG, hGsub, hmass, hloss, hstats⟩ := E.exists_measurable_era_set
    hBirkhoff hroot hB.1 hB1 hσ.le hσhalf hsmall hC0 hCi hL hsize
  refine ⟨T, hroot, hbranch, hdomain, ?_, G, hG, hGsub, hmass, ?_, hstats⟩
  · intro x n
    have hm := hmatch (T.word x n) (T.digits x n) (T.phase x (n + 1)) (T.phase_mem_domain x n)
    simpa only [T.phase_recurrence, ← T.word_succ] using hm
  · intro I
    simpa only [hroot] using hloss I

end BianchiIX
