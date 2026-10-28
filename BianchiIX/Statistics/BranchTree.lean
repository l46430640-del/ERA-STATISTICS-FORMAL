import BianchiIX.Statistics.StoppedMass

/-! Actual domains of a stopped inverse-branch tree. Only local branch data are assumed. -/

open Set MeasureTheory

namespace BianchiIX

structure InverseBranchTree where
  root : Set ℝ
  branch : List ℕ+ → ℕ+ → ℝ → ℝ
  domain : List ℕ+ → ℕ+ → Set ℝ
  root_open : IsOpen root
  domain_open : ∀ w a, IsOpen (domain w a)
  branch_continuous : ∀ w a, ContinuousOn (branch w a) (domain w a)
  branch_injective : ∀ w a, InjOn (branch w a) (domain w a)
  branch_disjoint : ∀ w, Pairwise (fun a b =>
    Disjoint (branch w a '' domain w a) (branch w b '' domain w b))

namespace InverseBranchTree

variable (T : InverseBranchTree)

def terminal (w : List ℕ+) : Set ℝ :=
  w.reverseRecOn T.root (fun v a K => T.domain v a ∩ T.branch v a ⁻¹' K)

def toRoot (w : List ℕ+) : ℝ → ℝ :=
  w.reverseRecOn id (fun v a H => H ∘ T.branch v a)

def cell (w : List ℕ+) : Set ℝ := T.toRoot w '' T.terminal w

def stoppedDomain (w : List ℕ+) : Set ℝ :=
  T.terminal w \ ⋃ a, T.branch w a '' T.domain w a

def level (n : ℕ) : Set ℝ := ⋃ w : {w : List ℕ+ // w.length = n}, T.cell w.val

@[simp] theorem terminal_nil : T.terminal [] = T.root := by
  simp [terminal, List.reverseRecOn]

@[simp] theorem terminal_append (w : List ℕ+) (a : ℕ+) :
    T.terminal (w ++ [a]) = T.domain w a ∩ T.branch w a ⁻¹' T.terminal w := by
  simp [terminal, List.reverseRecOn]

@[simp] theorem toRoot_nil : T.toRoot [] = id := by
  simp [toRoot, List.reverseRecOn]

@[simp] theorem toRoot_append (w : List ℕ+) (a : ℕ+) :
    T.toRoot (w ++ [a]) = T.toRoot w ∘ T.branch w a := by
  simp [toRoot, List.reverseRecOn]

@[simp] theorem cell_nil : T.cell [] = T.root := by simp [cell]

theorem terminal_open (w : List ℕ+) : IsOpen (T.terminal w) := by
  induction w using List.reverseRecOn with
  | nil => simpa using T.root_open
  | append_singleton w a ih =>
    rw [terminal_append]
    exact (T.branch_continuous w a).isOpen_inter_preimage (T.domain_open w a) ih

theorem toRoot_continuous (w : List ℕ+) : ContinuousOn (T.toRoot w) (T.terminal w) := by
  induction w using List.reverseRecOn with
  | nil => simpa using (continuousOn_id : ContinuousOn (id : ℝ → ℝ) T.root)
  | append_singleton w a ih =>
    rw [toRoot_append, terminal_append]
    exact ih.comp ((T.branch_continuous w a).mono inter_subset_left) (fun _ hx => hx.2)

theorem toRoot_injective (w : List ℕ+) : InjOn (T.toRoot w) (T.terminal w) := by
  induction w using List.reverseRecOn with
  | nil => simp
  | append_singleton w a ih =>
    rw [toRoot_append, terminal_append]
    intro x hx y hy hxy
    exact T.branch_injective w a hx.1 hy.1 (ih hx.2 hy.2 hxy)

theorem cell_measurable (w : List ℕ+) : MeasurableSet (T.cell w) :=
  (T.terminal_open w).measurableSet.image_of_continuousOn_injOn
    (T.toRoot_continuous w) (T.toRoot_injective w)

theorem stoppedDomain_measurable (w : List ℕ+) : MeasurableSet (T.stoppedDomain w) :=
  (T.terminal_open w).measurableSet.diff (MeasurableSet.iUnion (fun a =>
    (T.domain_open w a).measurableSet.image_of_continuousOn_injOn
      (T.branch_continuous w a) (T.branch_injective w a)))

theorem cell_append (w : List ℕ+) (a : ℕ+) :
    T.cell (w ++ [a]) = T.toRoot w ''
      (T.terminal w ∩ T.branch w a '' T.domain w a) := by
  ext x
  simp only [cell, toRoot_append, terminal_append, mem_image, mem_inter_iff,
    mem_preimage, Function.comp_apply]
  constructor
  · rintro ⟨y, ⟨hy, hK⟩, rfl⟩
    exact ⟨T.branch w a y, ⟨hK, y, hy, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨hK, y, hy, rfl⟩, rfl⟩
    exact ⟨y, ⟨hy, hK⟩, rfl⟩

theorem cell_child_subset (w : List ℕ+) (a : ℕ+) : T.cell (w ++ [a]) ⊆ T.cell w := by
  rw [cell_append]
  exact image_mono inter_subset_left

theorem cell_subset_of_prefix {v w : List ℕ+} (h : v <+: w) : T.cell w ⊆ T.cell v := by
  obtain ⟨u, rfl⟩ := h
  induction u using List.reverseRecOn with
  | nil => simp
  | append_singleton u a ih =>
    rw [← List.append_assoc]
    exact (T.cell_child_subset (v ++ u) a).trans ih

theorem cell_siblings_disjoint (w : List ℕ+) :
    Pairwise (fun a b => Disjoint (T.cell (w ++ [a])) (T.cell (w ++ [b]))) := by
  intro a b hab
  rw [T.cell_append, T.cell_append, Set.disjoint_left]
  rintro x ⟨u, ⟨hu, ha⟩, hux⟩ ⟨v, ⟨hv, hb⟩, hvx⟩
  have huv := T.toRoot_injective w hu hv (hux.trans hvx.symm)
  exact Set.disjoint_left.mp (T.branch_disjoint w hab) ha (huv ▸ hb)

theorem cell_unique {v w : List ℕ+} (hlen : v.length = w.length)
    {x : ℝ} (hv : x ∈ T.cell v) (hw : x ∈ T.cell w) : v = w := by
  induction v using List.reverseRecOn generalizing w with
  | nil =>
    have : w = [] := List.length_eq_zero_iff.mp hlen.symm
    exact this.symm
  | append_singleton v a ih =>
    induction w using List.reverseRecOn with
    | nil => simp at hlen
    | append_singleton w b _ =>
      have hvw : v = w := ih (by simpa using hlen)
        (T.cell_child_subset v a hv) (T.cell_child_subset w b hw)
      subst w
      have hab : a = b := by
        by_contra h
        exact Set.disjoint_left.mp (T.cell_siblings_disjoint v h) hv hw
      exact congrArg (fun c => v ++ [c]) hab

theorem mem_level {n : ℕ} {x : ℝ} :
    x ∈ T.level n ↔ ∃ w : List ℕ+, w.length = n ∧ x ∈ T.cell w := by
  simp [level]

@[simp] theorem level_zero : T.level 0 = T.root := by
  ext x
  simp [mem_level]

theorem level_succ (n : ℕ) :
    T.level (n + 1) = ⋃ w : {w : List ℕ+ // w.length = n}, ⋃ a, T.cell (w.val ++ [a]) := by
  ext x
  simp only [mem_level, mem_iUnion, Subtype.exists]
  constructor
  · rintro ⟨w, hw, hx⟩
    induction w using List.reverseRecOn with
    | nil => simp at hw
    | append_singleton w a _ => exact ⟨w, by simpa using hw, a, hx⟩
  · rintro ⟨w, hw, a, hx⟩
    exact ⟨w ++ [a], by simp [hw], hx⟩

theorem level_antitone : Antitone T.level := by
  apply antitone_nat_of_succ_le
  intro n x hx
  rw [level_succ] at hx
  obtain ⟨w, hx⟩ := mem_iUnion.mp hx
  obtain ⟨a, ha⟩ := mem_iUnion.mp hx
  exact T.mem_level.mpr ⟨w.val, w.property, T.cell_child_subset w.val a ha⟩

theorem level_measurable (n : ℕ) : MeasurableSet (T.level n) :=
  MeasurableSet.iUnion (fun w => T.cell_measurable w.val)

theorem stopped_image (w : List ℕ+) :
    T.toRoot w '' T.stoppedDomain w = T.cell w \ ⋃ a, T.cell (w ++ [a]) := by
  ext x
  constructor
  · rintro ⟨y, ⟨hy, hn⟩, rfl⟩
    refine ⟨⟨y, hy, rfl⟩, ?_⟩
    rintro hc
    obtain ⟨a, ha⟩ := mem_iUnion.mp hc
    rw [cell_append] at ha
    obtain ⟨z, ⟨hz, ha⟩, heq⟩ := ha
    have hzy := T.toRoot_injective w hz hy heq
    exact hn (mem_iUnion.mpr ⟨a, hzy ▸ ha⟩)
  · rintro ⟨⟨y, hy, rfl⟩, hn⟩
    refine ⟨y, ⟨hy, ?_⟩, rfl⟩
    rintro hc
    obtain ⟨a, ha⟩ := mem_iUnion.mp hc
    apply hn
    refine mem_iUnion.mpr ⟨a, ?_⟩
    rw [cell_append]
    exact ⟨y, ⟨hy, ha⟩, rfl⟩

theorem firstStopped_eq_images (n : ℕ) :
    firstStoppedSet T.level n =
      ⋃ w : {w : List ℕ+ // w.length = n}, T.toRoot w.val '' T.stoppedDomain w.val := by
  ext x
  simp only [firstStoppedSet, mem_sdiff, mem_iUnion]
  constructor
  · rintro ⟨hx, hn⟩
    obtain ⟨w, hw, hx⟩ := T.mem_level.mp hx
    refine ⟨⟨w, hw⟩, ?_⟩
    rw [stopped_image]
    refine ⟨hx, ?_⟩
    intro hc
    apply hn
    rw [level_succ]
    exact mem_iUnion.mpr ⟨⟨w, hw⟩, hc⟩
  · rintro ⟨⟨w, hw⟩, hx⟩
    rw [stopped_image] at hx
    refine ⟨T.mem_level.mpr ⟨w, hw, hx.1⟩, ?_⟩
    intro hc
    rw [level_succ] at hc
    obtain ⟨v, hc⟩ := mem_iUnion.mp hc
    obtain ⟨a, ha⟩ := mem_iUnion.mp hc
    have hvw : v.val = w := T.cell_unique (v.property.trans hw.symm)
      (T.cell_child_subset v.val a ha) hx.1
    exact hx.2 (mem_iUnion.mpr ⟨a, hvw ▸ ha⟩)

theorem root_sdiff_survivors :
    T.root \ survivingSet T.level =
      ⋃ n, ⋃ w : {w : List ℕ+ // w.length = n}, T.toRoot w.val '' T.stoppedDomain w.val := by
  rw [← T.level_zero, root_sdiff_survivingSet T.level T.level_antitone]
  simp_rw [T.firstStopped_eq_images]

end InverseBranchTree

end BianchiIX
