import BianchiIX.Statistics.DiscreteMass
import Mathlib.Tactic.Positivity

/-! Finite empirical distributions with a strictly positive sample size. -/

open Filter
open scoped Topology

namespace BianchiIX

noncomputable section
open scoped Classical

/-- The distribution of the first `N + 1` labels. -/
def empiricalMass {ι : Type*} (label : ℕ → ι) (N : ℕ) (i : ι) : ℝ :=
  ((N + 1 : ℕ) : ℝ)⁻¹ * ∑ j ∈ Finset.range (N + 1), if i = label j then 1 else 0

theorem empiricalMass_nonneg {ι : Type*} (label : ℕ → ι) (N : ℕ) (i : ι) :
    0 ≤ empiricalMass label N i := by
  unfold empiricalMass
  positivity

theorem empiricalMass_weighted_hasSum {ι : Type*} (label : ℕ → ι) (N : ℕ) (f : ι → ℝ) :
    HasSum (fun i => empiricalMass label N i * f i)
      (((N + 1 : ℕ) : ℝ)⁻¹ * ∑ j ∈ Finset.range (N + 1), f (label j)) := by
  have hj (j : ℕ) : HasSum (fun i => (if i = label j then (1 : ℝ) else 0) * f i) (f (label j)) := by
    convert! hasSum_ite_eq (label j) (f (label j)) using 1
    funext i
    split_ifs with h <;> simp [h]
  have h := (hasSum_sum (fun j (_ : j ∈ Finset.range (N + 1)) => hj j)).mul_left
    (((N + 1 : ℕ) : ℝ)⁻¹)
  simpa only [empiricalMass, mul_assoc, Finset.sum_mul] using h

theorem empiricalMass_hasSum {ι : Type*} (label : ℕ → ι) (N : ℕ) :
    HasSum (empiricalMass label N) 1 := by
  simpa [show (N : ℝ) + 1 ≠ 0 by positivity] using
    empiricalMass_weighted_hasSum label N (fun _ => 1)

end
end BianchiIX
