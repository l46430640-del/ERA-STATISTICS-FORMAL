import BianchiIX.Algebra.StableResidualCompactification
import Mathlib.Topology.Order.Compact

noncomputable section

namespace BianchiIX

open Set

theorem exists_stableResidualProfile_bounds :
    ∃ B > (0 : ℝ), ∀ p : Fin 2 → ℝ, (0 ≤ p 0 ∧ p 0 ≤ 2 / 5) → |p 1| ≤ 1 →
      ∀ i : Fin 4, |stableResidualProfile i p| ≤ B ∧
        ‖fderiv ℝ (stableResidualProfile i) p‖ ≤ B ∧
        ‖fderiv ℝ (fderiv ℝ (stableResidualProfile i)) p‖ ≤ B := by
  let S : Set (Fin 2 → ℝ) := Icc ![0, -1] ![2 / 5, 1]
  have hS : IsCompact S := isCompact_Icc
  let q := fun (p : Fin 2 → ℝ) (i : Fin 4) => |stableResidualProfile i p| +
    ‖fderiv ℝ (stableResidualProfile i) p‖ + ‖fderiv ℝ (fderiv ℝ (stableResidualProfile i)) p‖
  have hq (p : Fin 2 → ℝ) (i : Fin 4) : 0 ≤ q p i := by dsimp [q]; positivity
  have hcont (i : Fin 4) : ContinuousOn (fun p => q p i) S := by
    intro p hp
    have hreg := contDiffAt_stableResidualProfile 2 i (p := p) (by have H := hp.2 0; dsimp at H; linarith)
    have hreg' := hreg.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)
    exact ((hreg.continuousAt.abs.add (hreg.continuousAt_fderiv (by norm_num)).norm).add
      (hreg'.continuousAt_fderiv (by norm_num)).norm).continuousWithinAt
  have hsum : ContinuousOn (fun p => ∑ i : Fin 4, q p i) S :=
    continuousOn_finsetSum _ (fun i _ => hcont i)
  obtain ⟨B, hB⟩ := hS.exists_bound_of_continuousOn hsum
  refine ⟨max B 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro p hp hw i
  have hpS : p ∈ S := by
    constructor
    · intro j; fin_cases j
      · exact hp.1
      · exact (abs_le.mp hw).1
    · intro j; fin_cases j
      · exact hp.2
      · exact (abs_le.mp hw).2
  have H : q p i ≤ max B 1 :=
    (Finset.single_le_sum (fun j _ => hq p j) (Finset.mem_univ i)).trans
      ((le_abs_self _).trans ((hB p hpS).trans (le_max_left _ _)))
  dsimp [q] at H
  exact ⟨by linarith [norm_nonneg (fderiv ℝ (stableResidualProfile i) p),
      norm_nonneg (fderiv ℝ (fderiv ℝ (stableResidualProfile i)) p)],
    by linarith [abs_nonneg (stableResidualProfile i p),
      norm_nonneg (fderiv ℝ (fderiv ℝ (stableResidualProfile i)) p)],
    by linarith [abs_nonneg (stableResidualProfile i p), norm_nonneg (fderiv ℝ (stableResidualProfile i) p)]⟩

end BianchiIX
