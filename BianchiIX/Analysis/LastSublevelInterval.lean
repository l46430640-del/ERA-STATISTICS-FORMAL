import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.ByContra

noncomputable section

namespace BianchiIX

open Set

/-- The final strict sublevel interval ends either at the initial time or at level zero. -/
theorem exists_last_sublevel_interval {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Icc a b)) (hb : f b < 0) :
    ∃ c ∈ Ico a b, (c = a ∨ f c = 0) ∧
      (∀ t ∈ Icc c b, f t ≤ 0) ∧ ∀ t ∈ Ioc c b, f t < 0 := by
  let K := Icc a b ∩ f ⁻¹' Ici 0
  have hK : IsCompact K := isCompact_Icc.of_isClosed_subset
    (hf.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici) inter_subset_left
  obtain ⟨c, hc⟩ := (hK.insert a).exists_isGreatest (by simp)
  have hca : a ≤ c := hc.2 (mem_insert a K)
  have hcb : c < b := by
    rcases hc.1 with hca' | hcK
    · simpa only [hca'] using hab
    · exact lt_of_le_of_ne hcK.1.2 (by intro heq; subst c; exact (not_le_of_gt hb) hcK.2)
  have hright : ∀ t ∈ Ioc c b, f t < 0 := by
    intro t ht
    by_contra! hneg
    have htK : t ∈ K := ⟨⟨hca.trans ht.1.le, ht.2⟩, hneg⟩
    exact (not_le_of_gt ht.1) (hc.2 (mem_insert_of_mem a htK))
  have hclosed : IsClosed (Icc a b ∩ f ⁻¹' Iic 0) :=
    hf.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hclosure := closure_minimal (fun t (ht : t ∈ Ioc c b) =>
    show t ∈ Icc a b ∩ f ⁻¹' Iic 0 from ⟨⟨hca.trans ht.1.le, ht.2⟩, (hright t ht).le⟩) hclosed
  rw [closure_Ioc hcb.ne] at hclosure
  have hnonpos : ∀ t ∈ Icc c b, f t ≤ 0 := fun t ht => (hclosure ht).2
  refine ⟨c, ⟨hca, hcb⟩, ?_, hnonpos, hright⟩
  rcases hc.1 with hca' | hcK
  · exact Or.inl hca'
  · exact Or.inr (le_antisymm (hnonpos c ⟨le_rfl, hcb.le⟩) hcK.2)

end BianchiIX
