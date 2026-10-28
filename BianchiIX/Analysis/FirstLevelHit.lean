import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith

noncomputable section

namespace BianchiIX

open Set

/-- A continuous path from below to at least a level has a first hit with a strictly lower prefix. -/
theorem exists_first_level_hit {f : ℝ → ℝ} {a b h : ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Icc a b)) (ha : f a < h) (hb : h ≤ f b) :
    ∃ T ∈ Ioc a b, f T = h ∧ ∀ u ∈ Ico a T, f u < h := by
  let S : Set ℝ := Icc a b ∩ f ⁻¹' {h}
  have hclosed : IsClosed S := hf.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hcompact : IsCompact S := isCompact_Icc.of_isClosed_subset hclosed (fun _ hx => hx.1)
  obtain ⟨v, hv, heq⟩ := intermediate_value_Icc hab hf ⟨ha.le, hb⟩
  obtain ⟨T, hT, hleast⟩ := hcompact.exists_isLeast ⟨v, hv, heq⟩
  have hTa : a < T := lt_of_le_of_ne hT.1.1 (by
    intro heq
    have hh : f T = h := hT.2
    rw [← heq] at hh
    exact ha.ne hh)
  refine ⟨T, ⟨hTa, hT.1.2⟩, hT.2, ?_⟩
  intro u hu
  by_contra! hh
  obtain ⟨v, hv, hvh⟩ := intermediate_value_Icc hu.1
    (hf.mono (Icc_subset_Icc le_rfl (hu.2.le.trans hT.1.2))) ⟨ha.le, hh⟩
  have hTv := hleast (show v ∈ S from ⟨⟨hv.1, hv.2.trans (hu.2.le.trans hT.1.2)⟩, hvh⟩)
  exact (not_le_of_gt hu.2) (hTv.trans hv.2)

end BianchiIX
