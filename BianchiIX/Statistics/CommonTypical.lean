import BianchiIX.Statistics.ObservableTransfer
import Mathlib.Dynamics.BirkhoffSum.NormedSpace

/-! One measurable, exactly invariant typical set for a countable family of bounded observables. -/

open Set Filter MeasureTheory
open scoped Topology

namespace BianchiIX

def commonTypicalSet {X ι : Type*} (F : X → X) (f : ι → X → ℝ) (l : ι → ℝ) : Set X :=
  {x | ∀ i, Tendsto (fun n => birkhoffAverage ℝ F (f i) n x) atTop (𝓝 (l i))}

theorem measurable_birkhoffAverage {X : Type*} [MeasurableSpace X] {F : X → X} {f : X → ℝ}
    (hF : Measurable F) (hf : Measurable f) (n : ℕ) :
    Measurable (birkhoffAverage ℝ F f n) := by
  change Measurable (fun x => (n : ℝ)⁻¹ * ∑ j ∈ Finset.range n, f (F^[j] x))
  exact (Finset.measurable_sum _ (fun j _ => hf.comp (hF.iterate j))).const_mul _

theorem commonTypicalSet_measurable {X ι : Type*} [MeasurableSpace X] [Countable ι]
    {F : X → X} {f : ι → X → ℝ} (l : ι → ℝ)
    (hF : Measurable F) (hf : ∀ i, Measurable (f i)) : MeasurableSet (commonTypicalSet F f l) := by
  simp only [commonTypicalSet, ofPred_forall]
  exact MeasurableSet.iInter (fun i => measurableSet_tendsto_fun
    (fun n => measurable_birkhoffAverage hF (hf i) n) measurable_const)

theorem ae_mem_commonTypicalSet {X ι : Type*} [MeasurableSpace X] [Countable ι]
    (μ : Measure X) (F : X → X) (f : ι → X → ℝ) (l : ι → ℝ)
    (h : ∀ i, ∀ᵐ x ∂μ, Tendsto (fun n => birkhoffAverage ℝ F (f i) n x) atTop (𝓝 (l i))) :
    ∀ᵐ x ∂μ, x ∈ commonTypicalSet F f l := by
  exact ae_all_iff.mpr h

theorem commonTypicalSet_preimage {X ι : Type*} (F : X → X) (f : ι → X → ℝ) (l : ι → ℝ)
    (hf : ∀ i, Bornology.IsBounded (range (f i))) :
    F ⁻¹' commonTypicalSet F f l = commonTypicalSet F f l := by
  ext x
  change (∀ i, Tendsto (fun n => birkhoffAverage ℝ F (f i) n (F x)) atTop (𝓝 (l i))) ↔
    ∀ i, Tendsto (fun n => birkhoffAverage ℝ F (f i) n x) atTop (𝓝 (l i))
  constructor
  · intro h i
    have hd := tendsto_birkhoffAverage_apply_sub_birkhoffAverage' ℝ (hf i) F x
    simpa only [sub_sub_cancel, sub_zero] using (h i).sub hd
  · intro h i
    have hd := tendsto_birkhoffAverage_apply_sub_birkhoffAverage' ℝ (hf i) F x
    simpa only [sub_add_cancel, zero_add] using hd.add (h i)

theorem commonTypicalSet_iterate {X ι : Type*} (F : X → X) (f : ι → X → ℝ) (l : ι → ℝ)
    (hf : ∀ i, Bornology.IsBounded (range (f i))) (n : ℕ) (x : X) :
    F^[n] x ∈ commonTypicalSet F f l ↔ x ∈ commonTypicalSet F f l := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ← mem_preimage, commonTypicalSet_preimage F f l hf]
    exact ih

namespace InverseBranchTree.BranchEstimates

variable {T : InverseBranchTree} {d e : ℕ → ℝ} (E : T.BranchEstimates d e)

include E

theorem ae_code_property_on_unit {L : ℝ}
    (hbudget : ∀ n, (∑ j ∈ Finset.range n, (e j + if j = 0 then 0 else 2 * d j)) ≤ L)
    {P : ℝ → Prop} (hP : ∀ᵐ y ∂volume.restrict (Ioo (0 : ℝ) 1), P y) :
    ∀ᵐ x ∂(volume.comap (Subtype.val : T.survivors → ℝ)), P (T.code x) := by
  have hp := E.ae_code_property hbudget ((ae_restrict_iff' isOpen_Ioo.measurableSet).mp hP)
  filter_upwards [hp] with x hx
  exact hx ⟨gaussCode_pos (T.digits x), gaussCode_lt_one (T.digits x)⟩

theorem ae_code_commonTypical {ι : Type*} [Countable ι] {L : ℝ}
    (hbudget : ∀ n, (∑ j ∈ Finset.range n, (e j + if j = 0 then 0 else 2 * d j)) ≤ L)
    (F : ℝ → ℝ) (f : ι → ℝ → ℝ) (l : ι → ℝ)
    (h : ∀ i, ∀ᵐ y ∂volume.restrict (Ioo (0 : ℝ) 1),
      Tendsto (fun n => birkhoffAverage ℝ F (f i) n y) atTop (𝓝 (l i))) :
    ∀ᵐ x ∂(volume.comap (Subtype.val : T.survivors → ℝ)), T.code x ∈ commonTypicalSet F f l :=
  E.ae_code_property_on_unit hbudget (ae_mem_commonTypicalSet _ F f l h)

end InverseBranchTree.BranchEstimates
end BianchiIX
