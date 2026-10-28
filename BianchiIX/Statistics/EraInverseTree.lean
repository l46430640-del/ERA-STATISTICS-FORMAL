import BianchiIX.Dynamics.EraCurveFamily
import BianchiIX.Statistics.TreeDistortion

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal

def eraTreeDomain (σ B : ℝ) (w : List ℕ+) (a : ℕ+) : Set ℝ :=
  if a.natPred < ⌊1 / (eraAmplitude B w.length) ^ σ⌋₊ then
    Ioo (2 * (eraAmplitude B w.length) ^ σ) (1 - 2 * (eraAmplitude B w.length) ^ σ)
  else ∅

theorem mem_eraTreeDomain {σ B y : ℝ} {w : List ℕ+} {a : ℕ+} :
    y ∈ eraTreeDomain σ B w a ↔ a.natPred < ⌊1 / (eraAmplitude B w.length) ^ σ⌋₊ ∧
      y ∈ Ioo (2 * (eraAmplitude B w.length) ^ σ) (1 - 2 * (eraAmplitude B w.length) ^ σ) := by
  unfold eraTreeDomain
  split_ifs <;> simp_all

namespace EraCurve

def treeBranch (Γ : EraCurve) (η : ℝ) (J : ℕ) (σ B : ℝ) (w : List ℕ+) (a : ℕ+) : ℝ → ℝ :=
  eraInverseBranch η J a.natPred ((eraAmplitude B w.length) ^ σ)
    (Γ.family η J σ B w).U (Γ.family η J σ B w).W

theorem treeBranch_image_of_retained {Γ : EraCurve} {η σ B C : ℝ} {J : ℕ} {w : List ℕ+}
    (H : (Γ.family η J σ B w).StepEstimates η J σ (eraAmplitude B w.length) C)
    (a : ℕ+) (ha : a.natPred < ⌊1 / (eraAmplitude B w.length) ^ σ⌋₊) :
    Γ.treeBranch η J σ B w a '' eraTreeDomain σ B w a =
      Ioo (Γ.treeBranch η J σ B w a (1 - 2 * (eraAmplitude B w.length) ^ σ))
        (Γ.treeBranch η J σ B w a (2 * (eraAmplitude B w.length) ^ σ)) := by
  rw [eraTreeDomain, if_pos ha]
  exact H.branch_image_open a.natPred ha

def inverseTree (Γ : EraCurve) (η : ℝ) (J : ℕ) (σ B C : ℝ)
    (H : ∀ w : List ℕ+, (Γ.family η J σ B w).StepEstimates η J σ (eraAmplitude B w.length) C) :
    InverseBranchTree where
  root := Ioo 0 1
  branch := Γ.treeBranch η J σ B
  domain := eraTreeDomain σ B
  root_open := isOpen_Ioo
  domain_open := by intro w a; unfold eraTreeDomain; split_ifs <;> first | exact isOpen_Ioo | exact isOpen_empty
  branch_continuous := by
    intro w a y hy
    obtain ⟨ha, hy⟩ := mem_eraTreeDomain.mp hy
    exact (((H w).branch a.natPred ha).2 y ⟨hy.1.le, hy.2.le⟩).2.2.1.continuousAt.continuousWithinAt
  branch_injective := by
    intro w a x hx y hy hxy
    obtain ⟨ha, hx⟩ := mem_eraTreeDomain.mp hx
    obtain ⟨_, hy⟩ := mem_eraTreeDomain.mp hy
    exact ((H w).branch a.natPred ha).1.injOn ⟨hx.1.le, hx.2.le⟩ ⟨hy.1.le, hy.2.le⟩ hxy
  branch_disjoint := by
    intro w a b hab
    by_cases ha : a.natPred < ⌊1 / (eraAmplitude B w.length) ^ σ⌋₊
    · by_cases hb : b.natPred < ⌊1 / (eraAmplitude B w.length) ^ σ⌋₊
      · rw [treeBranch_image_of_retained (H w) a ha, treeBranch_image_of_retained (H w) b hb]
        exact (H w).branch_disjoint (Finset.mem_range.mpr ha) (Finset.mem_range.mpr hb)
          (fun he => hab (PNat.natPred_injective he))
      · have hd : eraTreeDomain σ B w b = ∅ := by rw [eraTreeDomain, if_neg hb]
        rw [hd, image_empty]
        simp
    · have hd : eraTreeDomain σ B w a = ∅ := by rw [eraTreeDomain, if_neg ha]
      rw [hd, image_empty]
      simp

theorem inverseTree_estimates {Γ : EraCurve} {η σ B C : ℝ} {J : ℕ}
    (hB : 0 < B) (hC : 0 ≤ C)
    (H : ∀ w : List ℕ+, (Γ.family η J σ B w).StepEstimates η J σ (eraAmplitude B w.length) C) :
    (Γ.inverseTree η J σ B C H).BranchEstimates (fun n => C * eraAmplitude B n)
      (fun n => 5 * C * Real.sqrt (eraAmplitude B n)) := by
  refine ⟨Subset.rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro w a y hy
    obtain ⟨_, hy⟩ := mem_eraTreeDomain.mp hy
    exact ⟨by linarith [(H w).beta_pos, hy.1], by linarith [(H w).beta_pos, hy.2]⟩
  · intro w a y hy
    obtain ⟨ha, hy⟩ := mem_eraTreeDomain.mp hy
    exact (((H w).branch a.natPred ha).2 y ⟨hy.1.le, hy.2.le⟩).2.2.1.differentiableAt (by norm_num)
  · intro w a y hy
    obtain ⟨ha, hy⟩ := mem_eraTreeDomain.mp hy
    exact (((H w).branch a.natPred ha).2 y ⟨hy.1.le, hy.2.le⟩).2.2.2.1.ne
  · intro w a y hy
    obtain ⟨ha, hy⟩ := mem_eraTreeDomain.mp hy
    have hv := (((H w).branch a.natPred ha).2 y ⟨hy.1.le, hy.2.le⟩).2.2.2.2.1
    have hden : 1 ≤ ((a.natPred : ℝ) + 1) ^ 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) a.natPred]
    have hb : 0 ≤ C * eraAmplitude B w.length := mul_nonneg hC (eraAmplitude_pos hB _).le
    have hcast : (a.natPred : ℝ) + 1 = (a : ℝ) := by exact_mod_cast a.natPred_add_one
    simpa only [inverseTree, treeBranch, hcast] using hv.trans (div_le_self hb hden)
  · intro w a y hy
    obtain ⟨ha, hy⟩ := mem_eraTreeDomain.mp hy
    have hcast : (a.natPred : ℝ) + 1 = (a : ℝ) := by exact_mod_cast a.natPred_add_one
    simpa only [inverseTree, treeBranch, hcast] using (((H w).branch a.natPred ha).2 y ⟨hy.1.le, hy.2.le⟩).2.2.2.2.2

theorem treeBranch_union {Γ : EraCurve} {η σ B C : ℝ} {J : ℕ} (w : List ℕ+)
    (H : (Γ.family η J σ B w).StepEstimates η J σ (eraAmplitude B w.length) C) :
    (⋃ a : ℕ+, Γ.treeBranch η J σ B w a '' eraTreeDomain σ B w a) =
      eraRetainedPhases η J ⌊1 / (eraAmplitude B w.length) ^ σ⌋₊ ((eraAmplitude B w.length) ^ σ)
        (Γ.family η J σ B w).U (Γ.family η J σ B w).W := by
  ext x
  constructor
  · intro hx
    obtain ⟨a, ha⟩ := mem_iUnion.mp hx
    have hret : a.natPred < ⌊1 / (eraAmplitude B w.length) ^ σ⌋₊ := by
      obtain ⟨y, hy, _⟩ := ha
      exact (mem_eraTreeDomain.mp hy).1
    rw [treeBranch_image_of_retained H a hret] at ha
    exact mem_iUnion₂.mpr ⟨a.natPred, Finset.mem_range.mpr hret, ha⟩
  · intro hx
    obtain ⟨m, hm, hxI⟩ := mem_iUnion₂.mp hx
    let a : ℕ+ := ⟨m + 1, Nat.succ_pos m⟩
    have ha : a.natPred = m := by simp [a, PNat.natPred]
    apply mem_iUnion.mpr
    refine ⟨a, ?_⟩
    rw [treeBranch_image_of_retained H a (by simpa [ha] using Finset.mem_range.mp hm)]
    simpa only [treeBranch, ha] using hxI

theorem inverseTree_stopped_volume {Γ : EraCurve} {η σ B C : ℝ} {J : ℕ}
    (hB : 0 < B) (hC : 0 ≤ C)
    (H : ∀ w : List ℕ+, (Γ.family η J σ B w).StepEstimates η J σ (eraAmplitude B w.length) C)
    (w : List ℕ+) :
    volume ((Γ.inverseTree η J σ B C H).stoppedDomain w) ≤
      ENNReal.ofReal (10 * (eraAmplitude B w.length) ^ σ) := by
  have hterminal := (inverseTree_estimates hB hC H).terminal_subset w
  have hsub : (Γ.inverseTree η J σ B C H).stoppedDomain w ⊆
      Ioo (0 : ℝ) 1 \ eraRetainedPhases η J ⌊1 / (eraAmplitude B w.length) ^ σ⌋₊
        ((eraAmplitude B w.length) ^ σ) (Γ.family η J σ B w).U (Γ.family η J σ B w).W := by
    intro x hx
    refine ⟨hterminal hx.1, ?_⟩
    rw [← treeBranch_union w (H w)]
    exact hx.2
  exact (measure_mono hsub).trans (H w).stopped_volume

theorem inverseTree_successor_match {Γ : EraCurve} {η σ B C : ℝ} {J : ℕ}
    (H : ∀ w : List ℕ+, (Γ.family η J σ B w).StepEstimates η J σ (eraAmplitude B w.length) C)
    (w : List ℕ+) (a : ℕ+) (y : ℝ)
    (hy : y ∈ (Γ.inverseTree η J σ B C H).domain w a) :
    let x := 2 / (Γ.inverseTree η J σ B C H).branch w a y
    let X := (Γ.family η J σ B w).state x
    eraOutputRadius η J a.natPred X = 2 / y ∧
      (Γ.family η J σ B (w ++ [a])).U (2 / y) = eraOutputState η J a.natPred X 1 ∧
      (Γ.family η J σ B (w ++ [a])).W (2 / y) = eraOutputState η J a.natPred X 3 := by
  obtain ⟨ha, hy⟩ := mem_eraTreeDomain.mp hy
  have hm := (H w).successor_match a.natPred ha y ⟨hy.1.le, hy.2.le⟩
  dsimp only
  rw [family_append_of_retained Γ η J σ B w a ha]
  exact hm

end EraCurve

/-- The inverse tree is built from the exact era maps and their extended successor curves. -/
theorem exists_era_inverse_tree :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 20 ≤ J → ∀ σ : ℝ, 0 < σ → σ < 1 → σ * (2 * J : ℕ) < 1 →
        ∃ C ≥ (1 : ℝ), ∃ Bstar > (0 : ℝ), Bstar < 1 ∧
          ∀ B ∈ Ioc 0 Bstar, ∀ Γ : EraCurve, Γ.Admissible B →
            ∃ T : InverseBranchTree, T.root = Ioo 0 1 ∧
              T.branch = Γ.treeBranch η J σ B ∧ T.domain = eraTreeDomain σ B ∧
              T.BranchEstimates (fun n => C * eraAmplitude B n)
                (fun n => 5 * C * Real.sqrt (eraAmplitude B n)) ∧
              (∀ w, volume (T.stoppedDomain w) ≤
                ENNReal.ofReal (10 * (eraAmplitude B w.length) ^ σ)) ∧
              ∀ w a y, y ∈ T.domain w a →
                let X := (Γ.family η J σ B w).state (2 / T.branch w a y)
                eraOutputRadius η J a.natPred X = 2 / y ∧
                  (Γ.family η J σ B (w ++ [a])).U (2 / y) = eraOutputState η J a.natPred X 1 ∧
                  (Γ.family η J σ B (w ++ [a])).W (2 / y) = eraOutputState η J a.natPred X 3 := by
  obtain ⟨δ, hδ, hδmax, Hδ⟩ := exists_era_curve_family
  refine ⟨δ, hδ, hδmax, ?_⟩
  intro η hη hηδ J hJ σ hσ hσone hσJ
  obtain ⟨C, hC, Bs, hBs, hBsone, H⟩ := Hδ η hη hηδ J hJ σ hσ hσone hσJ
  refine ⟨C, hC, Bs, hBs, hBsone, ?_⟩
  intro B hB Γ hΓ
  have Hnodes w := (H B hB Γ hΓ w).2
  exact ⟨Γ.inverseTree η J σ B C Hnodes, rfl, rfl, rfl,
    EraCurve.inverseTree_estimates hB.1 (by linarith) Hnodes,
    EraCurve.inverseTree_stopped_volume hB.1 (by linarith) Hnodes,
    EraCurve.inverseTree_successor_match Hnodes⟩

end BianchiIX
