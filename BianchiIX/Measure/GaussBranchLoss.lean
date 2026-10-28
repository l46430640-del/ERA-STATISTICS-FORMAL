import BianchiIX.Analysis.GaussBranchLengths
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal

def retainedBranchPhases (N : ℕ) (L R : ℕ → ℝ) : Set ℝ :=
  ⋃ m ∈ Finset.range N, Ioo (R m) (L m)

/-- Summable endpoint errors give a finite-digit loss bound, including all removed endpoints. -/
theorem finite_gauss_branch_loss {N : ℕ} {β E : ℝ} {L R : ℕ → ℝ}
    (hβ : 0 ≤ β) (hβmax : β ≤ 1 / 2) (hE : 0 ≤ E)
    (horder : ∀ m ∈ Finset.range N, R m < L m)
    (hlower : ∀ m ∈ Finset.range N, 1 / ((m : ℝ) + 2) < R m)
    (hupper : ∀ m ∈ Finset.range N, L m < 1 / ((m : ℝ) + 1))
    (hL : ∀ m ∈ Finset.range N,
      |L m - gaussInv ((m : ℝ) + 1) (2 * β)| ≤ E / ((m : ℝ) + 1) ^ 2)
    (hR : ∀ m ∈ Finset.range N,
      |R m - gaussInv ((m : ℝ) + 1) (1 - 2 * β)| ≤ E / ((m : ℝ) + 1) ^ 2) :
    (↑(Finset.range N) : Set ℕ).PairwiseDisjoint (fun m => Ioo (R m) (L m)) ∧
    MeasurableSet (Ioo (0 : ℝ) 1 \ retainedBranchPhases N L R) ∧
    volume (Ioo (0 : ℝ) 1 \ retainedBranchPhases N L R) ≤
      ENNReal.ofReal (1 / ((N : ℝ) + 1) + 8 * β + 4 * E) := by
  have hdisjlt (i j : ℕ) (hi : i ∈ Finset.range N) (hj : j ∈ Finset.range N) (hij : i < j) :
      Disjoint (Ioo (R i) (L i)) (Ioo (R j) (L j)) := by
    apply disjoint_left.mpr
    intro x hxi hxj
    have hcast : (i : ℝ) + 2 ≤ (j : ℝ) + 1 := by exact_mod_cast (show i + 2 ≤ j + 1 by omega)
    have hrec : 1 / ((j : ℝ) + 1) ≤ 1 / ((i : ℝ) + 2) :=
      one_div_le_one_div_of_le (by positivity) hcast
    linarith [hlower i hi, hupper j hj, hxi.1, hxj.2]
  have hdisj : (↑(Finset.range N) : Set ℕ).PairwiseDisjoint (fun m => Ioo (R m) (L m)) := by
    intro i hi j hj hij
    rcases lt_or_gt_of_ne hij with hij | hji
    · exact hdisjlt i j hi hj hij
    · exact (hdisjlt j i hj hi hji).symm
  have hmeas : MeasurableSet (retainedBranchPhases N L R) :=
    (Finset.finite_toSet _).measurableSet_biUnion (fun _ _ => measurableSet_Ioo)
  have hsub : retainedBranchPhases N L R ⊆ Ioo (0 : ℝ) 1 := by
    intro x hx
    obtain ⟨m, hm, hxm⟩ := mem_iUnion₂.mp hx
    have hrec : 1 / ((m : ℝ) + 1) ≤ 1 :=
      (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) m])
    exact ⟨(by positivity : (0 : ℝ) < 1 / ((m : ℝ) + 2)).trans
      ((hlower m hm).trans hxm.1), (hxm.2.trans (hupper m hm)).trans_le hrec⟩
  let S := ∑ m ∈ Finset.range N, (L m - R m)
  have hnonneg (m : ℕ) (hm : m ∈ Finset.range N) : 0 ≤ L m - R m := sub_nonneg.mpr (horder m hm).le
  have hS : 0 ≤ S := Finset.sum_nonneg hnonneg
  have hvol : volume (retainedBranchPhases N L R) = ENNReal.ofReal S := by
    rw [retainedBranchPhases, measure_biUnion_finset hdisj (fun _ _ => measurableSet_Ioo)]
    simp_rw [Real.volume_Ioo]
    exact (ENNReal.ofReal_sum_of_nonneg hnonneg).symm
  have hwidth (m : ℕ) (hm : m ∈ Finset.range N) :
      1 / ((m : ℝ) + 1) - 1 / ((m : ℝ) + 2) -
        (4 * β + 2 * E) / ((m : ℝ) + 1) ^ 2 ≤ L m - R m := by
    simpa only [show (m : ℝ) + 1 + 1 = (m : ℝ) + 2 by ring] using
      gauss_branch_length_of_endpoint_error (by positivity : 0 < (m : ℝ) + 1)
        hβ hβmax (hL m hm) (hR m hm)
  have hsum := Finset.sum_le_sum hwidth
  have hcoeff : 0 ≤ 4 * β + 2 * E := by positivity
  have hweights := mul_le_mul_of_nonneg_left (sum_inverse_square_digits_le_two N) hcoeff
  have hformula : (∑ m ∈ Finset.range N,
      (1 / ((m : ℝ) + 1) - 1 / ((m : ℝ) + 2) - (4 * β + 2 * E) / ((m : ℝ) + 1) ^ 2)) =
      1 - 1 / ((N : ℝ) + 1) - (4 * β + 2 * E) *
        (∑ m ∈ Finset.range N, 1 / ((m : ℝ) + 1) ^ 2) := by
    rw [Finset.sum_sub_distrib, sum_gauss_digit_lengths, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro m _
    ring
  rw [hformula] at hsum
  have htotal : 1 ≤ S + (1 / ((N : ℝ) + 1) + 8 * β + 4 * E) := by
    change _ ≤ S at hsum
    linarith
  have hfinite : volume (retainedBranchPhases N L R) ≠ ∞ := by rw [hvol]; exact ENNReal.ofReal_ne_top
  refine ⟨hdisj, measurableSet_Ioo.diff hmeas, ?_⟩
  apply (measure_sdiff_le_iff_le_add hmeas.nullMeasurableSet hsub hfinite).mpr
  rw [hvol, ← ENNReal.ofReal_add hS (by positivity), Real.volume_Ioo]
  exact ENNReal.ofReal_le_ofReal (by simpa using htotal)

end BianchiIX
