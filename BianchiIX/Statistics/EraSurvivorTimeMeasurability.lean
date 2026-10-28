import BianchiIX.Statistics.CoreRestartOrbit
import BianchiIX.Dynamics.EraTimeRegularity

noncomputable section

namespace BianchiIX

open Set MeasureTheory

namespace EraSurvivor

variable {η σ Bcap : ℝ} {J : ℕ}
variable (H : ∀ m : ℕ, MeasurableSet (eraSelectedInputs η J σ Bcap m) ∧
  Measurable (fun p : eraSelectedInputs η J σ Bcap m => eraBudgetReturn η J m p.val))

include H

theorem frame_measurable :
    Measurable (frame (η := η) (J := J) (σ := σ) (Bcap := Bcap)) := by
  apply measurable_pi_lambda
  intro n
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    have hc : Measurable (fun v : Fin 6 × ℕ+ => (axisFrame_comp (eraReturnFrame v.2.natPred) v.1).choose) :=
      measurable_of_countable _
    change Measurable (fun p : eraSurvivorDomain η J σ Bcap =>
      (axisFrame_comp (eraReturnFrame (digits p n).natPred) (frame p n)).choose)
    have hd : Measurable (fun p : eraSurvivorDomain η J σ Bcap => digits p n) :=
      (measurable_pi_apply n).comp (digits_measurable H)
    have hpair : Measurable (fun p : eraSurvivorDomain η J σ Bcap => (frame p n, digits p n)) := ih.prodMk hd
    convert hc.comp hpair using 1
    rfl

theorem physicalFrame_measurable :
    Measurable (fun v : CoreRestartData × eraSurvivorDomain η J σ Bcap => physicalFrame v.1 v.2) := by
  have hc : Measurable (fun v : Fin 6 × Fin 6 => (axisFrame_comp v.1 v.2).choose) :=
    measurable_of_countable _
  apply measurable_pi_lambda
  intro n
  exact hc.comp ((((measurable_pi_apply n).comp (frame_measurable H)).comp measurable_snd).prodMk
    measurable_fst.fst.fst)

variable (HT : ∀ m : ℕ, ∀ p ∈ eraSelectedInputs η J σ Bcap m,
  ContDiffAt ℝ 1 (eraReturnTime η J m) p.2)

include HT

/-- Extend only the restricted actual time maps, then evaluate at the measurable selected digit and state. -/
theorem duration_measurable :
    Measurable (duration (η := η) (J := J) (σ := σ) (Bcap := Bcap)) := by
  have hm (m : ℕ) : Measurable (fun p : eraSelectedInputs η J σ Bcap m => eraReturnTime η J m p.val.2) :=
    measurable_comp_of_continuousAt (measurable_snd.comp measurable_subtype_coe)
      (fun p => (HT m p.val p.property).continuousAt)
  choose f hf heq using fun m : ℕ =>
    (MeasurableEmbedding.subtype_coe (H m).1).exists_measurable_extend (hm m) (fun _ => inferInstance)
  have hjoint : Measurable (fun v : ℕ × (ℝ × CoreAngleState) => f v.1 v.2) :=
    measurable_from_prod_countable_right hf
  apply measurable_pi_lambda
  intro n
  have hd : Measurable (fun p : eraSurvivorDomain η J σ Bcap => (digits p n).natPred) :=
    (measurable_of_countable (fun a : ℕ+ => a.natPred)).comp
      ((measurable_pi_apply n).comp (digits_measurable H))
  have hstate := (measurable_pi_apply n).comp (budgetState_measurable H)
  have hcomp := hjoint.comp (hd.prodMk hstate)
  convert hcomp using 1
  funext p
  exact (congrFun (heq (digits p n).natPred) ⟨budgetState p n, budgetState_mem_selected p n⟩).symm

theorem elapsedTime_measurable :
    Measurable (elapsedTime (η := η) (J := J) (σ := σ) (Bcap := Bcap)) := by
  apply measurable_pi_lambda
  intro n
  exact Finset.measurable_sum _ (fun j _ => (measurable_pi_apply j).comp (duration_measurable H HT))

theorem physicalTime_measurable :
    Measurable (fun v : CoreRestartData × eraSurvivorDomain η J σ Bcap => physicalTime v.1 v.2) := by
  apply measurable_pi_lambda
  intro n
  exact (((measurable_pi_apply n).comp (elapsedTime_measurable H HT)).comp measurable_snd).add
    measurable_fst.fst.snd

end EraSurvivor
end BianchiIX
