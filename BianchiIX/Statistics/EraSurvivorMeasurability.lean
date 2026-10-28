import BianchiIX.Statistics.EraCodingRealization

noncomputable section

namespace BianchiIX

open Set MeasureTheory

local instance : MeasurableSpace (List ℕ+) := ⊤

namespace EraSurvivor

variable {η σ Bcap : ℝ} {J : ℕ}

def budgetState (p : eraSurvivorDomain η J σ Bcap) (n : ℕ) : ℝ × CoreAngleState :=
  eraPrefixState η J (word p n) p.val

def state (p : eraSurvivorDomain η J σ Bcap) (n : ℕ) : CoreAngleState := (budgetState p n).2

theorem budgetState_zero (p : eraSurvivorDomain η J σ Bcap) : budgetState p 0 = p.val := by
  have hw : word p 0 = [] := List.length_eq_zero_iff.mp (word_length p 0)
  simp only [budgetState, hw, eraPrefixState, id_eq]

theorem budgetState_succ (p : eraSurvivorDomain η J σ Bcap) (n : ℕ) :
    budgetState p (n + 1) = eraBudgetReturn η J (digits p n).natPred (budgetState p n) := by
  unfold budgetState
  rw [word_succ, eraPrefixState_append]
  rfl

theorem budgetState_mem_selected (p : eraSurvivorDomain η J σ Bcap) (n : ℕ) :
    budgetState p n ∈ eraSelectedInputs η J σ Bcap (digits p n).natPred := by
  have H := mem_word_domain p (n + 1)
  rw [word_succ] at H
  exact ((mem_eraPrefixDomain_append η J σ Bcap (word p n) [digits p n] p.val).mp H).2.1

variable (H : ∀ m : ℕ, MeasurableSet (eraSelectedInputs η J σ Bcap m) ∧
  Measurable (fun p : eraSelectedInputs η J σ Bcap m => eraBudgetReturn η J m p.val))

include H

theorem word_measurable (n : ℕ) :
    Measurable (fun p : eraSurvivorDomain η J σ Bcap => word p n) := by
  apply measurable_to_countable'
  intro w
  change MeasurableSet {p : eraSurvivorDomain η J σ Bcap | word p n = w}
  by_cases hw : w.length = n
  · have heq : {p : eraSurvivorDomain η J σ Bcap | word p n = w} =
        Subtype.val ⁻¹' eraPrefixDomain η J σ Bcap w := by
      ext p
      exact word_eq_iff p hw
    rw [heq]
    exact (eraPrefixDomain_measurable H w).1.preimage measurable_subtype_coe
  · have heq : {p : eraSurvivorDomain η J σ Bcap | word p n = w} = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro p hp
      exact hw (hp ▸ word_length p n)
    rw [heq]
    exact MeasurableSet.empty

/-- Only the measurable restricted finite-history maps are extended; no regularity is assumed on invalid inputs. -/
theorem budgetState_measurable :
    Measurable (budgetState (η := η) (J := J) (σ := σ) (Bcap := Bcap)) := by
  choose f hf heq using fun w : List ℕ+ =>
    (MeasurableEmbedding.subtype_coe (eraPrefixDomain_measurable H w).1).exists_measurable_extend
      (eraPrefixDomain_measurable H w).2 (fun _ => inferInstance)
  have hm : Measurable (fun v : List ℕ+ × (ℝ × CoreAngleState) => f v.1 v.2) :=
    measurable_from_prod_countable_right hf
  apply measurable_pi_lambda
  intro n
  have hcomp := hm.comp ((word_measurable H n).prodMk measurable_subtype_coe)
  convert hcomp using 1
  funext p
  exact (congrFun (heq (word p n)) ⟨p.val, mem_word_domain p n⟩).symm

theorem state_measurable :
    Measurable (state (η := η) (J := J) (σ := σ) (Bcap := Bcap)) := by
  apply measurable_pi_lambda
  intro n
  exact ((measurable_pi_apply n).comp (budgetState_measurable H)).snd

theorem phase_measurable :
    Measurable (phase (η := η) (J := J) (σ := σ) (Bcap := Bcap)) := by
  apply measurable_pi_lambda
  intro n
  exact measurable_const.div ((measurable_pi_apply 0).comp
    ((measurable_pi_apply n).comp (state_measurable H)))

end EraSurvivor
end BianchiIX
