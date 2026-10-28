import BianchiIX.Algebra.SectionBounds
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Compactness.Compact

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

/-- Local finiteness on bounded initial intervals makes the first visit an attained minimum. -/
theorem exists_least_of_finite_initial_intervals {S : Set ℝ} {a : ℝ}
    (hS : S ⊆ Ici a) (hne : S.Nonempty) (hfinite : ∀ b, (S ∩ Icc a b).Finite) :
    ∃ t, IsLeast S t := by
  obtain ⟨b, hb⟩ := hne
  obtain ⟨t, ht, hmin⟩ := Set.exists_min_image (S ∩ Icc a b) id (hfinite b) ⟨b, hb, hS hb, le_rfl⟩
  refine ⟨t, ht.1, fun u hu => ?_⟩
  by_cases hub : u ≤ b
  · exact hmin u ⟨hu, hS hu, hub⟩
  · exact ht.2.2.trans (le_of_not_ge hub)

/-- A nonzero derivative isolates each point of a compact constant-level set. -/
theorem finite_compact_transverse_level {K : Set ℝ} {f df : ℝ → ℝ} {h : ℝ}
    (hK : IsCompact K) (hlevel : ∀ t ∈ K, f t = h)
    (hderiv : ∀ t ∈ K, HasDerivAt f (df t) t) (hne : ∀ t ∈ K, df t ≠ 0) : K.Finite := by
  apply hK.finite
  rw [isDiscrete_iff_nhdsNE]
  intro t ht
  rw [inf_principal_eq_bot]
  have H : ∀ᶠ u in 𝓝[≠] t, slope f t u ≠ 0 :=
    (hderiv t ht).tendsto_slope.eventually (eventually_ne_nhds (hne t ht))
  filter_upwards [H] with u hu
  intro huK
  exact hu (by simp [slope, hlevel u huK, hlevel t ht])

theorem finite_negative_section_times {K : Set ℝ} {a p s : ℝ → ℝ} {h ε : ℝ}
    (hK : IsCompact K) (ha : ContinuousOn a K) (hp : ContinuousOn p K)
    (hh : 0 < h) (hε : 0 < ε)
    (hODE : ∀ t ∈ K, HasDerivAt a (rateOne (p t) (s t) * a t) t) :
    {t ∈ K | a t = h ∧ p t ≤ -ε}.Finite := by
  let S : Set ℝ := {t ∈ K | a t = h ∧ p t ≤ -ε}
  have hS : IsCompact S := by
    obtain ⟨U, hU, heq⟩ := continuousOn_iff_isClosed.mp (ha.prodMk hp)
      ({h} ×ˢ Iic (-ε)) (isClosed_singleton.prod isClosed_Iic)
    have H : IsCompact ((fun t => (a t, p t)) ⁻¹' ({h} ×ˢ Iic (-ε)) ∩ K) := by
      rw [heq]
      exact hK.inter_left hU
    convert! H using 1
    ext t
    simp only [S, mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_prod, mem_singleton_iff, mem_Iic]
    tauto
  apply finite_compact_transverse_level (df := fun t => rateOne (p t) (s t) * a t) hS
    (fun t ht => ht.2.1) (fun t ht => hODE t ht.1)
  intro t ht
  have hpt : p t ≤ -ε := ht.2.2
  have hr : rateOne (p t) (s t) < 0 := by
    unfold rateOne shearSq
    nlinarith [sq_nonneg (p t), sq_nonneg (s t)]
  exact ne_of_lt (mul_neg_of_neg_of_pos hr (ht.2.1 ▸ hh))

def smallSectionTimes (K : Set ℝ) (h : ℝ) (p s a b c : ℝ → ℝ) : Set ℝ :=
  {t ∈ K | a t = h ∧ p t < 0 ∧ |s t| ≤ 1 / 8 ∧
    0 ≤ b t ∧ b t ≤ h / 8 ∧ 0 ≤ c t ∧ c t ≤ h / 8}

theorem finite_small_section_times {K : Set ℝ} {p s a b c : ℝ → ℝ} {h : ℝ}
    (hK : IsCompact K) (ha : ContinuousOn a K) (hp : ContinuousOn p K)
    (hh : 0 < h) (hh1 : h ≤ 1 / 8)
    (hconstraint : ∀ t ∈ K, constraint (p t) (s t) (a t) (b t) (c t) = 1)
    (hODE : ∀ t ∈ K, HasDerivAt a (rateOne (p t) (s t) * a t) t) :
    (smallSectionTimes K h p s a b c).Finite := by
  apply (finite_negative_section_times (ε := 15 / 16) hK ha hp hh (by norm_num) hODE).subset
  intro t ht
  rcases ht with ⟨htK, hat, hpt, hst, hbt, hbt1, hct, hct1⟩
  refine ⟨htK, hat, ?_⟩
  have hcon : constraint (p t) (s t) h (b t) (c t) = 1 := by
    simpa only [hat] using hconstraint t htK
  simpa only [neg_div] using (small_section_bounds hh hh1 hbt hct hbt1 hct1 hst hpt hcon).2.2.1

end BianchiIX
