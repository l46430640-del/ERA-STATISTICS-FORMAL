import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

/-- A closed real interval in an open set has an open interval neighborhood in that set. -/
theorem exists_Ioo_covering_Icc {s t : ℝ} {U : Set ℝ} (hst : s ≤ t)
    (hU : IsOpen U) (hsub : Icc s t ⊆ U) :
    ∃ l r : ℝ, l < s ∧ t < r ∧ Ioo l r ⊆ U := by
  obtain ⟨l, v, hs, hl⟩ := mem_nhds_iff_exists_Ioo_subset.mp
    (hU.mem_nhds (hsub ⟨le_rfl, hst⟩))
  obtain ⟨u, r, ht, hr⟩ := mem_nhds_iff_exists_Ioo_subset.mp
    (hU.mem_nhds (hsub ⟨hst, le_rfl⟩))
  refine ⟨l, r, hs.1, ht.2, ?_⟩
  intro x hx
  by_cases hxs : x < s
  · exact hl ⟨hx.1, hxs.trans hs.2⟩
  by_cases htx : t < x
  · exact hr ⟨ht.1.trans htx, hx.2⟩
  exact hsub ⟨le_of_not_gt hxs, le_of_not_gt htx⟩

theorem exists_Ioo_covering_of_eventually {s t : ℝ} {P : ℝ → Prop} (hst : s ≤ t)
    (hP : ∀ u ∈ Icc s t, ∀ᶠ v in 𝓝 u, P v) :
    ∃ l r : ℝ, l < s ∧ t < r ∧ ∀ u ∈ Ioo l r, P u := by
  obtain ⟨l, r, hls, htr, hsub⟩ := exists_Ioo_covering_Icc hst isOpen_interior
    (fun u hu => mem_interior_iff_mem_nhds.mpr (hP u hu))
  exact ⟨l, r, hls, htr, fun u hu => interior_subset (hsub hu)⟩

end BianchiIX
