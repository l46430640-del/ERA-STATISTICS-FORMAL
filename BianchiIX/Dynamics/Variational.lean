import BianchiIX.Dynamics.Linearization

noncomputable section

namespace BianchiIX

open Set Filter Metric
open scoped Topology NNReal

theorem hasDerivAt_normalizedTangent_components
    {α : ℝ → NormalizedState × NormalizedVariation} {t : ℝ}
    (hα : HasDerivAt α (normalizedTangentField (α t)) t) :
    HasDerivAt (fun u => (α u).1) (normalizedField (α t).1) t ∧
      HasDerivAt (fun u => (α u).2) ((normalizedDifferential (α t).1).comp (α t).2) t := by
  constructor
  · exact (ContinuousLinearMap.fst ℝ NormalizedState NormalizedVariation).hasFDerivAt.comp_hasDerivAt t hα
  · exact (ContinuousLinearMap.snd ℝ NormalizedState NormalizedVariation).hasFDerivAt.comp_hasDerivAt t hα

/-- Construct a continuous family solving the variational equation along the actual maximal flow. -/
theorem exists_normalized_variation_family (x₀ : NormalizedState) (t₀ : ℝ) :
    ∃ r > (0 : ℝ), ∃ ε > (0 : ℝ), ∃ J : NormalizedState × ℝ → NormalizedVariation,
      ContinuousOn J (closedBall x₀ r ×ˢ Ioo (t₀ - ε) (t₀ + ε)) ∧
      ∀ x ∈ closedBall x₀ r,
        Ioo (t₀ - ε) (t₀ + ε) ⊆ normalizedMaxDomain x t₀ ∧
        J (x, t₀) = ContinuousLinearMap.id ℝ NormalizedState ∧
        ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε),
          HasDerivAt (fun u => J (x, u))
            ((normalizedDifferential (normalizedMaxCurve x t₀ t)).comp (J (x, t))) t := by
  let idE := ContinuousLinearMap.id ℝ NormalizedState
  obtain ⟨ε, hε, a, r, L, K, hr, hPL⟩ := IsPicardLindelof.of_contDiffAt_one
    ((contDiff_normalizedTangentField 1).contDiffAt (x := (x₀, idE)))
  obtain ⟨Φ, hΦ, hcΦ⟩ := (hPL t₀).exists_forall_mem_closedBall_eq_hasDerivWithinAt_continuousOn
  have hxpair (x : NormalizedState) (hx : x ∈ closedBall x₀ r) :
      (x, idE) ∈ closedBall (x₀, idE) r := by
    simpa only [mem_closedBall, dist_prod_same_right] using hx
  have hode (x : NormalizedState) (hx : x ∈ closedBall x₀ r)
      (t : ℝ) (ht : t ∈ Ioo (t₀ - ε) (t₀ + ε)) :
      HasDerivAt (fun u => Φ ((x, idE), u)) (normalizedTangentField (Φ ((x, idE), t))) t :=
    ((hΦ (x, idE) (hxpair x hx)).2 t (Ioo_subset_Icc_self ht)).hasDerivAt
      (Icc_mem_nhds ht.1 ht.2)
  have ht₀ : t₀ ∈ Ioo (t₀ - ε) (t₀ + ε) := by constructor <;> linarith
  let S (x : NormalizedState) (hx : x ∈ closedBall x₀ r) : NormalizedSolution x t₀ :=
    ⟨Ioo (t₀ - ε) (t₀ + ε), isOpen_Ioo, convex_Ioo _ _, ht₀,
      fun t => (Φ ((x, idE), t)).1,
      congrArg Prod.fst (hΦ (x, idE) (hxpair x hx)).1,
      fun t ht => (hasDerivAt_normalizedTangent_components (hode x hx t ht)).1⟩
  let J : NormalizedState × ℝ → NormalizedVariation := fun z => (Φ ((z.1, idE), z.2)).2
  refine ⟨r, hr, ε, hε, J, ?_, fun x hx => ?_⟩
  · apply continuous_snd.comp_continuousOn
    apply hcΦ.comp (by fun_prop : ContinuousOn (fun z : NormalizedState × ℝ => ((z.1, idE), z.2)) _)
    intro z hz
    exact ⟨hxpair z.1 hz.1, Ioo_subset_Icc_self hz.2⟩
  · refine ⟨(S x hx).domain_subset_maximal, congrArg Prod.snd (hΦ (x, idE) (hxpair x hx)).1, ?_⟩
    intro t ht
    have heq := normalizedMaxCurve_eqOn (S x hx) ht
    rw [heq]
    exact (hasDerivAt_normalizedTangent_components (hode x hx t ht)).2

end BianchiIX
