import BianchiIX.Dynamics.Continuation

noncomputable section

namespace BianchiIX

open Set Filter Metric
open scoped Topology

/-- An exact solution on an open interval containing its initial time. -/
structure NormalizedSolution (x₀ : NormalizedState) (t₀ : ℝ) where
  domain : Set ℝ
  isOpen_domain : IsOpen domain
  convex_domain : Convex ℝ domain
  initial_mem : t₀ ∈ domain
  curve : ℝ → NormalizedState
  initial_eq : curve t₀ = x₀
  hasDerivAt : ∀ t ∈ domain, HasDerivAt curve (normalizedField (curve t)) t

theorem nonempty_normalizedSolution (x₀ : NormalizedState) (t₀ : ℝ) :
    Nonempty (NormalizedSolution x₀ t₀) := by
  obtain ⟨α, hinit, ε, hε, hα⟩ := exists_normalized_solution x₀ t₀
  exact ⟨⟨Ioo (t₀ - ε) (t₀ + ε), isOpen_Ioo, convex_Ioo _ _,
    by constructor <;> linarith, α, hinit, fun t ht => (hα t ht).1⟩⟩

theorem NormalizedSolution.compatible {x₀ : NormalizedState} {t₀ : ℝ}
    (S T : NormalizedSolution x₀ t₀) : EqOn S.curve T.curve (S.domain ∩ T.domain) :=
  normalized_solution_unique (S.convex_domain.inter T.convex_domain)
    (fun t ht => S.hasDerivAt t ht.1) (fun t ht => T.hasDerivAt t ht.2)
    ⟨S.initial_mem, T.initial_mem⟩ (S.initial_eq.trans T.initial_eq.symm)

def normalizedMaxDomain (x₀ : NormalizedState) (t₀ : ℝ) : Set ℝ :=
  ⋃ S : NormalizedSolution x₀ t₀, S.domain

def normalizedMaxCurve (x₀ : NormalizedState) (t₀ t : ℝ) : NormalizedState := by
  classical
  exact if h : t ∈ normalizedMaxDomain x₀ t₀ then
    (mem_iUnion.mp h).choose.curve t else x₀

theorem NormalizedSolution.domain_subset_maximal {x₀ : NormalizedState} {t₀ : ℝ}
    (S : NormalizedSolution x₀ t₀) : S.domain ⊆ normalizedMaxDomain x₀ t₀ :=
  subset_iUnion (fun T : NormalizedSolution x₀ t₀ => T.domain) S

theorem normalizedMaxCurve_eqOn {x₀ : NormalizedState} {t₀ : ℝ}
    (S : NormalizedSolution x₀ t₀) : EqOn (normalizedMaxCurve x₀ t₀) S.curve S.domain := by
  classical
  intro t ht
  have hmem := S.domain_subset_maximal ht
  simp only [normalizedMaxCurve, dif_pos hmem]
  exact ((mem_iUnion.mp hmem).choose.compatible S) ⟨(mem_iUnion.mp hmem).choose_spec, ht⟩

theorem isOpen_normalizedMaxDomain (x₀ : NormalizedState) (t₀ : ℝ) :
    IsOpen (normalizedMaxDomain x₀ t₀) :=
  isOpen_iUnion fun S => S.isOpen_domain

theorem convex_normalizedMaxDomain (x₀ : NormalizedState) (t₀ : ℝ) :
    Convex ℝ (normalizedMaxDomain x₀ t₀) := by
  rw [convex_iff_ordConnected]
  refine ⟨fun x hx y hy z hz => ?_⟩
  obtain ⟨S, hx⟩ := mem_iUnion.mp hx
  obtain ⟨T, hy⟩ := mem_iUnion.mp hy
  have hzST := (convex_union_real S.convex_domain T.convex_domain
    S.initial_mem T.initial_mem).ordConnected.out (Or.inl hx) (Or.inr hy) hz
  exact (union_subset S.domain_subset_maximal T.domain_subset_maximal) hzST

theorem initial_mem_normalizedMaxDomain (x₀ : NormalizedState) (t₀ : ℝ) :
    t₀ ∈ normalizedMaxDomain x₀ t₀ := by
  obtain ⟨S⟩ := nonempty_normalizedSolution x₀ t₀
  exact S.domain_subset_maximal S.initial_mem

theorem normalizedMaxCurve_initial (x₀ : NormalizedState) (t₀ : ℝ) :
    normalizedMaxCurve x₀ t₀ t₀ = x₀ := by
  obtain ⟨S⟩ := nonempty_normalizedSolution x₀ t₀
  exact (normalizedMaxCurve_eqOn S S.initial_mem).trans S.initial_eq

theorem hasDerivAt_normalizedMaxCurve {x₀ : NormalizedState} {t₀ t : ℝ}
    (ht : t ∈ normalizedMaxDomain x₀ t₀) :
    HasDerivAt (normalizedMaxCurve x₀ t₀) (normalizedField (normalizedMaxCurve x₀ t₀ t)) t := by
  obtain ⟨S, ht⟩ := mem_iUnion.mp ht
  rw [normalizedMaxCurve_eqOn S ht]
  exact (S.hasDerivAt t ht).congr_of_eventuallyEq
    (Filter.eventuallyEq_of_mem (S.isOpen_domain.mem_nhds ht)
      fun u hu => normalizedMaxCurve_eqOn S hu)

/-- The union of all compatible local solutions is itself a solution. -/
def maximalNormalizedSolution (x₀ : NormalizedState) (t₀ : ℝ) : NormalizedSolution x₀ t₀ where
  domain := normalizedMaxDomain x₀ t₀
  isOpen_domain := isOpen_normalizedMaxDomain x₀ t₀
  convex_domain := convex_normalizedMaxDomain x₀ t₀
  initial_mem := initial_mem_normalizedMaxDomain x₀ t₀
  curve := normalizedMaxCurve x₀ t₀
  initial_eq := normalizedMaxCurve_initial x₀ t₀
  hasDerivAt := fun _ ht => hasDerivAt_normalizedMaxCurve ht

theorem normalizedMaxDomain_contains_extension {x₀ : NormalizedState} {t₀ s : ℝ}
    {J : Set ℝ} (hJ : Convex ℝ J) (hoJ : IsOpen J)
    {β : ℝ → NormalizedState}
    (hβ : ∀ t ∈ J, HasDerivAt β (normalizedField (β t)) t)
    (hs : s ∈ normalizedMaxDomain x₀ t₀) (hsJ : s ∈ J)
    (heq : normalizedMaxCurve x₀ t₀ s = β s) : J ⊆ normalizedMaxDomain x₀ t₀ := by
  let S := maximalNormalizedSolution x₀ t₀
  obtain ⟨γ, hγS, _, hγ⟩ := normalized_solution_glue
    S.convex_domain S.isOpen_domain hJ hoJ S.hasDerivAt hβ hs hsJ heq
  let T : NormalizedSolution x₀ t₀ :=
    ⟨S.domain ∪ J, S.isOpen_domain.union hoJ,
      convex_union_real S.convex_domain hJ hs hsJ, Or.inl S.initial_mem,
      γ, (hγS S.initial_mem).trans S.initial_eq, hγ⟩
  exact subset_union_right.trans T.domain_subset_maximal

end BianchiIX
