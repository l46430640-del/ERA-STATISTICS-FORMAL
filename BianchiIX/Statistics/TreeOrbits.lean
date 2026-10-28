import BianchiIX.Statistics.TreeDistortion

/-! Actual intermediate phases of surviving initial points and their Gauss comparison. -/

open Set MeasureTheory Filter
open scoped Topology

namespace BianchiIX
namespace InverseBranchTree

variable (T : InverseBranchTree)

private theorem exists_phase (x : T.survivors) (n : ℕ) :
    ∃ t ∈ T.terminal (T.word x n), T.toRoot (T.word x n) t = x.val :=
  T.mem_word_cell x n

noncomputable def phase (x : T.survivors) (n : ℕ) : ℝ := (T.exists_phase x n).choose

theorem phase_mem_terminal (x : T.survivors) (n : ℕ) :
    T.phase x n ∈ T.terminal (T.word x n) := (T.exists_phase x n).choose_spec.1

theorem toRoot_phase (x : T.survivors) (n : ℕ) :
    T.toRoot (T.word x n) (T.phase x n) = x.val := (T.exists_phase x n).choose_spec.2

@[simp] theorem phase_zero (x : T.survivors) : T.phase x 0 = x.val := by
  have hw : T.word x 0 = [] := List.length_eq_zero_iff.mp (T.word_length x 0)
  simpa only [hw, T.toRoot_nil, id_eq] using T.toRoot_phase x 0

theorem phase_mem_domain (x : T.survivors) (n : ℕ) :
    T.phase x (n + 1) ∈ T.domain (T.word x n) (T.digits x n) := by
  have hx := T.phase_mem_terminal x (n + 1)
  rw [T.word_succ, T.terminal_append] at hx
  exact hx.1

theorem phase_recurrence (x : T.survivors) (n : ℕ) :
    T.branch (T.word x n) (T.digits x n) (T.phase x (n + 1)) = T.phase x n := by
  have hx := T.phase_mem_terminal x (n + 1)
  rw [T.word_succ, T.terminal_append] at hx
  apply T.toRoot_injective (T.word x n) hx.2 (T.phase_mem_terminal x n)
  have hn := T.toRoot_phase x (n + 1)
  rw [T.word_succ, T.toRoot_append] at hn
  exact hn.trans (T.toRoot_phase x n).symm

namespace BranchEstimates

variable {T : InverseBranchTree} {d e : ℕ → ℝ} (E : T.BranchEstimates d e)

include E

theorem phase_mem_unit (x : T.survivors) (n : ℕ) : T.phase x n ∈ Icc (0 : ℝ) 1 :=
  ⟨(E.terminal_subset (T.word x n) (T.phase_mem_terminal x n)).1.le,
    (E.terminal_subset (T.word x n) (T.phase_mem_terminal x n)).2.le⟩

theorem phase_error_le (x : T.survivors) (n : ℕ) :
    inverseError (fun k => (T.digits x k : ℕ)) (T.phase x) n ≤ d n := by
  have h := E.value_error (T.word x n) (T.digits x n) (T.phase x (n + 1)) (T.phase_mem_domain x n)
  simpa only [T.phase_recurrence, T.word_length, inverseError] using h

theorem phase_shadowing (hd : Tendsto d atTop (𝓝 0)) (x : T.survivors) :
    Tendsto (fun n => T.phase x n - gaussMap^[n] (T.code x)) atTop (𝓝 0) := by
  apply gaussCode_shadowing (T.digits x) (E.phase_mem_unit x)
  exact squeeze_zero (fun n => abs_nonneg _) (E.phase_error_le x) hd

theorem phase_error_summable (hd : Summable d) (x : T.survivors) :
    Summable (fun n => |T.phase x n - gaussMap^[n] (T.code x)|) ∧
      (∑' n, |T.phase x n - gaussMap^[n] (T.code x)|) ≤ (8 / 3) * ∑' n, d n := by
  have hs : Summable (inverseError (fun k => (T.digits x k : ℕ)) (T.phase x)) :=
    Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (E.phase_error_le x) hd
  have h := gaussCode_error_summable (T.digits x) (E.phase_mem_unit x) hs
  refine ⟨h.1, h.2.trans ?_⟩
  exact mul_le_mul_of_nonneg_left (hs.tsum_le_tsum (E.phase_error_le x) hd) (by norm_num)

end BranchEstimates
end InverseBranchTree
end BianchiIX
