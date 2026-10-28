import BianchiIX.Statistics.BranchTree

/-! Measurable symbolic coding of the surviving points of an actual inverse-branch tree. -/

open Set MeasureTheory
open scoped NNReal ENNReal

namespace BianchiIX
namespace InverseBranchTree

variable (T : InverseBranchTree)

def survivors : Set ℝ := survivingSet T.level

theorem survivors_measurable : MeasurableSet T.survivors :=
  measurableSet_survivingSet T.level T.level_measurable

private theorem exists_word (x : T.survivors) (n : ℕ) :
    ∃ w : List ℕ+, w.length = n ∧ x.val ∈ T.cell w :=
  T.mem_level.mp (mem_iInter.mp x.property n)

noncomputable def word (x : T.survivors) (n : ℕ) : List ℕ+ :=
  (T.exists_word x n).choose

theorem word_length (x : T.survivors) (n : ℕ) : (T.word x n).length = n :=
  (T.exists_word x n).choose_spec.1

theorem mem_word_cell (x : T.survivors) (n : ℕ) : x.val ∈ T.cell (T.word x n) :=
  (T.exists_word x n).choose_spec.2

theorem word_eq_iff (x : T.survivors) {n : ℕ} {w : List ℕ+} (hw : w.length = n) :
    T.word x n = w ↔ x.val ∈ T.cell w := by
  constructor
  · intro h
    simpa only [h] using T.mem_word_cell x n
  · exact fun h => T.cell_unique ((T.word_length x n).trans hw.symm) (T.mem_word_cell x n) h

private theorem exists_next_digit (x : T.survivors) (n : ℕ) :
    ∃ a : ℕ+, T.word x (n + 1) = T.word x n ++ [a] := by
  have hl := T.word_length x (n + 1)
  have hx := T.mem_word_cell x (n + 1)
  generalize T.word x (n + 1) = w at hl hx ⊢
  induction w using List.reverseRecOn with
  | nil => simp at hl
  | append_singleton w a _ =>
    have hw : w = T.word x n := T.cell_unique (by simpa [T.word_length] using hl)
      (T.cell_child_subset w a hx) (T.mem_word_cell x n)
    exact ⟨a, congrArg (fun v => v ++ [a]) hw⟩

noncomputable def digits (x : T.survivors) (n : ℕ) : ℕ+ :=
  (T.exists_next_digit x n).choose

theorem word_succ (x : T.survivors) (n : ℕ) :
    T.word x (n + 1) = T.word x n ++ [T.digits x n] :=
  (T.exists_next_digit x n).choose_spec

theorem digits_prefix (x : T.survivors) (n : ℕ) :
    digitPrefix (T.digits x) n = (T.word x n).map (fun a : ℕ+ => (a : ℕ)) := by
  induction n with
  | zero =>
    have hw : T.word x 0 = [] := List.length_eq_zero_iff.mp (T.word_length x 0)
    simp [digitPrefix, hw]
  | succ n ih =>
    rw [T.word_succ, List.map_append, List.map_singleton, ← ih]
    simp [digitPrefix, List.range_succ]

theorem digit_fiber (n : ℕ) (a : ℕ+) :
    {x : T.survivors | T.digits x n = a} =
      ⋃ w : {w : List ℕ+ // w.length = n},
        (Subtype.val : T.survivors → ℝ) ⁻¹' T.cell (w.val ++ [a]) := by
  ext x
  simp only [mem_ofPred_eq, mem_iUnion, mem_preimage]
  constructor
  · intro h
    refine ⟨⟨T.word x n, T.word_length x n⟩, ?_⟩
    have hx := T.mem_word_cell x (n + 1)
    simpa only [T.word_succ, h] using hx
  · rintro ⟨⟨w, hw⟩, hx⟩
    have heq := (T.word_eq_iff x (by simp [hw] : (w ++ [a]).length = n + 1)).mpr hx
    rw [T.word_succ] at heq
    exact List.singleton_inj.mp (List.append_inj_right heq ((T.word_length x n).trans hw.symm))

theorem digits_measurable : Measurable T.digits := by
  apply measurable_pi_lambda
  intro n
  apply measurable_to_countable'
  intro a
  change MeasurableSet {x : T.survivors | T.digits x n = a}
  rw [T.digit_fiber]
  exact MeasurableSet.iUnion (fun w => (T.cell_measurable (w.val ++ [a])).preimage measurable_subtype_coe)

theorem prefix_fiber (w : List ℕ+) :
    {x : T.survivors | digitPrefix (T.digits x) w.length = w.map (fun a : ℕ+ => (a : ℕ))} =
      (Subtype.val : T.survivors → ℝ) ⁻¹' T.cell w := by
  ext x
  simp only [mem_ofPred_eq, mem_preimage, T.digits_prefix]
  constructor
  · intro h
    apply (T.word_eq_iff x rfl).mp
    exact List.map_injective_iff.mpr Subtype.val_injective h
  · intro h
    rw [(T.word_eq_iff x rfl).mpr h]

noncomputable def code (x : T.survivors) : ℝ := gaussCode (T.digits x)

theorem code_measurable : Measurable T.code := measurable_gaussCode.comp T.digits_measurable

theorem code_irrational (x : T.survivors) : Irrational (T.code x) := gaussCode_irrational _

private theorem positive_word_lift (w : List ℕ) (hw : ∀ k ∈ w, 1 ≤ k) :
    ∃ v : List ℕ+, v.map (fun a : ℕ+ => (a : ℕ)) = w := by
  induction w with
  | nil => exact ⟨[], rfl⟩
  | cons k w ih =>
    obtain ⟨v, hv⟩ := ih (fun j hj => hw j (List.mem_cons_of_mem k hj))
    refine ⟨⟨k, hw k (by simp)⟩ :: v, ?_⟩
    change k :: v.map (fun a : ℕ+ => (a : ℕ)) = k :: w
    rw [hv]

theorem code_map_le_of_cell_bounds (μ ν : Measure ℝ) [ν.OuterRegular] (C : ℝ≥0)
    (hbound : ∀ w : List ℕ+, w ≠ [] →
      μ (T.cell w) ≤ (C : ℝ≥0∞) * ν (gaussCylinder (w.map (fun a : ℕ+ => (a : ℕ))))) :
    Measure.map T.code (μ.comap (Subtype.val : T.survivors → ℝ)) ≤ C • ν := by
  apply gaussCode_map_le_smul_of_cylinder_bounds _ ν T.digits T.digits_measurable C
  intro w hwne hw
  obtain ⟨v, hv⟩ := positive_word_lift w hw
  have hlen : v.length = w.length := by simpa using congrArg List.length hv
  have hvne : v ≠ [] := by
    intro hz
    subst v
    exact hwne (by simpa using hv.symm)
  rw [← hlen, ← hv, T.prefix_fiber]
  rw [comap_subtype_coe_apply T.survivors_measurable]
  exact (measure_mono (image_preimage_subset _ _)).trans (hbound v hvne)

theorem code_map_absolutelyContinuous (μ ν : Measure ℝ) [ν.OuterRegular] (C : ℝ≥0)
    (hbound : ∀ w : List ℕ+, w ≠ [] →
      μ (T.cell w) ≤ (C : ℝ≥0∞) * ν (gaussCylinder (w.map (fun a : ℕ+ => (a : ℕ))))) :
    Measure.map T.code (μ.comap (Subtype.val : T.survivors → ℝ)) ≪ ν := by
  intro s hs
  have h := Measure.le_iff'.mp (T.code_map_le_of_cell_bounds μ ν C hbound) s
  simpa only [Measure.smul_apply, hs, smul_zero, nonpos_iff_eq_zero] using h

end InverseBranchTree
end BianchiIX
