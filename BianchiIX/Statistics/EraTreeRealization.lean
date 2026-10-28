import BianchiIX.Statistics.EraInverseTree
import BianchiIX.Statistics.EraSurvivorCoding

noncomputable section

namespace BianchiIX

open Set

namespace EraCurve

def treeState (Γ : EraCurve) (η : ℝ) (J : ℕ) (σ B : ℝ) (w : List ℕ+) (x : ℝ) : ℝ × CoreAngleState :=
  (eraAmplitude B w.length, (Γ.family η J σ B w).state (2 / x))

@[simp] theorem treeState_nil (Γ : EraCurve) (η : ℝ) (J : ℕ) (σ B x : ℝ) :
    Γ.treeState η J σ B [] x = (B, Γ.state (2 / x)) := by simp [treeState]

/-- Agreement of the selected forward return with every edge of an inverse tree. -/
structure Realization (Γ : EraCurve) (η : ℝ) (J : ℕ) (σ B Bcap : ℝ) (T : InverseBranchTree) : Prop where
  root : T.root = Ioo 0 1
  step : ∀ w a y, y ∈ T.domain w a →
    eraBudgetReturn η J a.natPred (Γ.treeState η J σ B w (T.branch w a y)) =
      Γ.treeState η J σ B (w ++ [a]) y
  selected : ∀ w a x, Γ.treeState η J σ B w x ∈ eraSelectedInputs η J σ Bcap a.natPred ↔
    x ∈ T.branch w a '' T.domain w a

theorem realization_of_estimates {Γ : EraCurve} {η σ B Bcap C : ℝ} {J : ℕ}
    (hB : B ∈ Ioc 0 Bcap) (hcap : Bcap ≤ 1)
    (H : ∀ w : List ℕ+, (Γ.family η J σ B w).Admissible (eraAmplitude B w.length) ∧
      (Γ.family η J σ B w).StepEstimates η J σ (eraAmplitude B w.length) C)
    (Hselect : ∀ b ∈ Ioc 0 Bcap, ∀ γ : EraCurve, γ.Admissible b →
      ∀ m : ℕ, m < ⌊1 / b ^ σ⌋₊ → ∀ x : ℝ,
        (b, γ.state (2 / x)) ∈ eraSelectedInputs η J σ Bcap m ↔
          x ∈ eraInverseBranch η J m (b ^ σ) γ.U γ.W '' Ioo (2 * b ^ σ) (1 - 2 * b ^ σ)) :
    Γ.Realization η J σ B Bcap (Γ.inverseTree η J σ B C (fun w => (H w).2)) := by
  refine ⟨rfl, ?_, ?_⟩
  · intro w a y hy
    have hm := inverseTree_successor_match (fun w => (H w).2) w a y hy
    apply Prod.ext
    · change (eraAmplitude B w.length) ^ (4 / 3 : ℝ) = eraAmplitude B (w ++ [a]).length
      rw [List.length_append, List.length_singleton, eraAmplitude_succ hB.1.le]
    · funext i
      fin_cases i
      · exact hm.1
      · exact hm.2.1.symm
      · exact hm.2.2.symm
  · intro w a x
    have hb : eraAmplitude B w.length ∈ Ioc 0 Bcap :=
      ⟨eraAmplitude_pos hB.1 _, (eraAmplitude_le hB.1.le (hB.2.trans hcap) _).trans hB.2⟩
    by_cases ha : a.natPred < ⌊1 / (eraAmplitude B w.length) ^ σ⌋₊
    · change (eraAmplitude B w.length, (Γ.family η J σ B w).state (2 / x)) ∈ _ ↔
        x ∈ Γ.treeBranch η J σ B w a '' eraTreeDomain σ B w a
      rw [eraTreeDomain, if_pos ha]
      exact Hselect _ hb _ (H w).1 a.natPred ha x
    · have hd : (Γ.inverseTree η J σ B C (fun w => (H w).2)).domain w a = ∅ := by
        change eraTreeDomain σ B w a = ∅
        rw [eraTreeDomain, if_neg ha]
      rw [hd, image_empty, mem_empty_iff_false, iff_false]
      exact fun hx => ha hx.1.2.1

namespace Realization

variable {Γ : EraCurve} {η σ B Bcap : ℝ} {J : ℕ} {T : InverseBranchTree}
variable (R : Γ.Realization η J σ B Bcap T)

include R

theorem prefix_state (w : List ℕ+) (y : ℝ) (hy : y ∈ T.terminal w) :
    eraPrefixState η J w (B, Γ.state (2 / T.toRoot w y)) = Γ.treeState η J σ B w y := by
  induction w using List.reverseRecOn generalizing y with
  | nil => simp [eraPrefixState]
  | append_singleton w a ih =>
    rw [T.terminal_append] at hy
    rw [eraPrefixState_append, T.toRoot_append]
    change eraBudgetReturn η J a.natPred
      (eraPrefixState η J w (B, Γ.state (2 / T.toRoot w (T.branch w a y)))) = _
    rw [ih _ hy.2]
    exact R.step w a y hy.1

theorem prefix_domain_iff_cell (w : List ℕ+) (x : ℝ) (hx : x ∈ T.root) :
    (B, Γ.state (2 / x)) ∈ eraPrefixDomain η J σ Bcap w ↔ x ∈ T.cell w := by
  induction w using List.reverseRecOn with
  | nil => simp [eraPrefixDomain, hx]
  | append_singleton w a ih =>
    rw [mem_eraPrefixDomain_append, T.cell_append]
    simp only [eraPrefixDomain, mem_inter_iff, mem_preimage, mem_univ, and_true]
    constructor
    · rintro ⟨hp, hnext⟩
      obtain ⟨z, hz, hzx⟩ := ih.mp hp
      have hs := R.prefix_state w z hz
      rw [hzx] at hs
      rw [hs] at hnext
      exact ⟨z, ⟨hz, (R.selected w a z).mp hnext⟩, hzx⟩
    · rintro ⟨z, ⟨hz, hnext⟩, hzx⟩
      refine ⟨ih.mpr ⟨z, hz, hzx⟩, ?_⟩
      have hs := R.prefix_state w z hz
      rw [hzx] at hs
      rw [hs]
      exact (R.selected w a z).mpr hnext

theorem survivor_iff (x : ℝ) (hx : x ∈ T.root) :
    (B, Γ.state (2 / x)) ∈ eraSurvivorDomain η J σ Bcap ↔ x ∈ T.survivors := by
  constructor
  · intro hp
    apply mem_iInter.mpr
    intro n
    obtain ⟨w, hw⟩ := mem_iUnion.mp (mem_iInter.mp hp n)
    exact T.mem_level.mpr ⟨w.val, w.property, (R.prefix_domain_iff_cell w.val x hx).mp hw⟩
  · intro hp
    apply mem_iInter.mpr
    intro n
    obtain ⟨w, hw, hc⟩ := T.mem_level.mp (mem_iInter.mp hp n)
    exact mem_iUnion.mpr ⟨⟨w, hw⟩, (R.prefix_domain_iff_cell w x hx).mpr hc⟩

end Realization
end EraCurve
end BianchiIX
