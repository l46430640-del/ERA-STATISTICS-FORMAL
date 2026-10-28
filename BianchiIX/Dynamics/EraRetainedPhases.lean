import BianchiIX.Dynamics.EraInverseBranch
import BianchiIX.Analysis.RetainedEraParameters
import BianchiIX.Measure.GaussBranchLoss
import Mathlib.Algebra.Order.Floor.Semiring

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal

def eraRetainedPhases (η : ℝ) (J N : ℕ) (β : ℝ) (U W : ℝ → ℝ) : Set ℝ :=
  retainedBranchPhases N (fun m => eraInverseBranch η J m β U W (2 * β))
    (fun m => eraInverseBranch η J m β U W (1 - 2 * β))

/-- All retained actual digits share one threshold; their open intervals lose at most ten phase margins. -/
theorem exists_era_retained_phase_loss :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 4 ≤ J → ∀ σ : ℝ, 0 < σ → σ < 1 → σ * (2 * J : ℕ) < 1 →
        ∃ C ≥ (1 : ℝ), ∃ Bstar > (0 : ℝ), Bstar < 1 ∧
        ∀ B ∈ Ioc 0 Bstar, ∀ U W : ℝ → ℝ,
          (∀ r : ℝ, 2 < r → 0 < U r ∧ 0 < W r ∧ U r + W r ≤ B ∧
            ContDiffAt ℝ 1 U r ∧ ContDiffAt ℝ 1 W r ∧
            |deriv U r| ≤ Real.sqrt (U r) ∧ |deriv W r| ≤ Real.sqrt (W r)) →
          let β := B ^ σ
          let N := ⌊1 / β⌋₊
          let K := Icc (2 * β) (1 - 2 * β)
          let h := fun m => eraInverseBranch η J m β U W
          0 < β ∧ β < 1 / 160 ∧
          (∀ m ∈ Finset.range N, StrictAntiOn (h m) K ∧
            h m '' K = Icc (h m (1 - 2 * β)) (h m (2 * β)) ∧
            ∀ y ∈ K, h m y ∈ Ioo (1 / ((m : ℝ) + 2)) (1 / ((m : ℝ) + 1)) ∧
              graphPhase (eraBoundedPhase η J m) U W (2 / h m y) = y ∧
              ContDiffAt ℝ 1 (h m) y ∧ deriv (h m) y < 0 ∧
              |h m y - gaussInv ((m : ℝ) + 1) y| ≤ C * B / ((m : ℝ) + 1) ^ 2 ∧
              |Real.log (|deriv (h m) y| / |deriv (gaussInv ((m : ℝ) + 1)) y|)| ≤
                5 * C * Real.sqrt B) ∧
          (↑(Finset.range N) : Set ℕ).PairwiseDisjoint
            (fun m => Ioo (h m (1 - 2 * β)) (h m (2 * β))) ∧
          MeasurableSet (Ioo (0 : ℝ) 1 \ eraRetainedPhases η J N β U W) ∧
          volume (Ioo (0 : ℝ) 1 \ eraRetainedPhases η J N β U W) ≤ ENNReal.ofReal (10 * β) := by
  obtain ⟨δ, hδ, hδmax, H⟩ := exists_era_inverse_branch_estimates
  refine ⟨δ, hδ, hδmax, ?_⟩
  intro η hη hηδ J hJ σ hσ hσone hσJ
  obtain ⟨ε, hε, _, C, hC, HE⟩ := H η hη hηδ J hJ
  have hC0 : 0 ≤ C := by linarith
  obtain ⟨Bstar, hBs, hBsone, HB⟩ := exists_retained_era_parameter_budget hε hC0 hσ hσone hσJ
  refine ⟨C, hC, Bstar, hBs, hBsone, ?_⟩
  intro B hB U W Hgraph β N K h
  obtain ⟨hβ, hβmax, hsmall, hmargin, hscale⟩ := HB B hB
  change 0 < β at hβ
  change β < 1 / 160 at hβmax
  change B ≤ ε * (β / 2) ^ (2 * J) at hsmall
  change C * B < β / 4 at hmargin
  have hJends : 2 * β < 1 - 2 * β := by linarith
  have hleft : 2 * β ∈ K := ⟨le_rfl, hJends.le⟩
  have hright : 1 - 2 * β ∈ K := ⟨hJends.le, le_rfl⟩
  have hcap (m : ℕ) (hm : m ∈ Finset.range N) : (m : ℝ) + 1 ≤ 1 / β := by
    have hnat : m + 1 ≤ N := Nat.succ_le_of_lt (Finset.mem_range.mp hm)
    have hcast : (m : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast hnat
    exact hcast.trans (Nat.floor_le (by positivity))
  have Hbranch (m : ℕ) (hm : m ∈ Finset.range N) :=
    HE m β B U W hβ (by linarith) (hscale m (hcap m hm)) hsmall hmargin (by
      intro r hr
      apply Hgraph r
      nlinarith [hr.1, Nat.cast_nonneg (α := ℝ) m])
  have Hloss := finite_gauss_branch_loss (N := N) hβ.le (by linarith) (mul_nonneg hC0 hB.1.le)
    (L := fun m => h m (2 * β)) (R := fun m => h m (1 - 2 * β))
    (fun m hm => (Hbranch m hm).1 hleft hright hJends)
    (fun m hm => ((Hbranch m hm).2 _ hright).1.1)
    (fun m hm => ((Hbranch m hm).2 _ hleft).1.2)
    (fun m hm => ((Hbranch m hm).2 _ hleft).2.2.2.2.1)
    (fun m hm => ((Hbranch m hm).2 _ hright).2.2.2.2.1)
  have htail : 1 / ((N : ℝ) + 1) < β := by
    have Hfloor := Nat.lt_floor_add_one (1 / β)
    have Hmul := (div_lt_iff₀ hβ).mp Hfloor
    exact (div_lt_iff₀ (by positivity : (0 : ℝ) < (N : ℝ) + 1)).mpr (by nlinarith)
  refine ⟨hβ, hβmax, ?_, Hloss.1, Hloss.2.1, Hloss.2.2.trans ?_⟩
  · intro m hm
    have hcont : ContinuousOn (h m) K :=
      fun y hy => ((Hbranch m hm).2 y hy).2.2.1.continuousAt.continuousWithinAt
    exact ⟨(Hbranch m hm).1,
      hcont.image_Icc_of_antitoneOn hJends.le (Hbranch m hm).1.antitoneOn, (Hbranch m hm).2⟩
  · apply ENNReal.ofReal_le_ofReal
    nlinarith

end BianchiIX
