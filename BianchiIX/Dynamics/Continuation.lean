import BianchiIX.Dynamics.LocalFlow

noncomputable section

namespace BianchiIX

open Set Filter Metric
open scoped Topology NNReal

/-- A bounded set of initial states has a common positive existence time. -/
theorem exists_normalized_solution_uniform (R : ℝ) (hR : 0 ≤ R) :
    ∃ ε > (0 : ℝ), ∀ x : NormalizedState, ‖x‖ ≤ R → ∀ t₀ : ℝ,
      ∃ α : ℝ → NormalizedState, α t₀ = x ∧
        ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε), HasDerivAt α (normalizedField (α t)) t := by
  obtain ⟨K, hK⟩ := normalizedField_lipschitz_closedBall 0 (R + 1)
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : NormalizedState) (R + 1)).exists_bound_of_continuousOn
    (contDiff_normalizedField 1).continuous.continuousOn
  let L : ℝ≥0 := ⟨max B 0, le_max_right _ _⟩
  let a : ℝ≥0 := ⟨R + 1, by positivity⟩
  let r : ℝ≥0 := ⟨R, hR⟩
  let ε : ℝ := 1 / (L + 1)
  have hε : 0 < ε := by dsimp [ε]; positivity
  refine ⟨ε, hε, fun x hx t₀ => ?_⟩
  have hPL : IsPicardLindelof (fun _ => normalizedField)
      (tmin := t₀ - ε) (tmax := t₀ + ε) ⟨t₀, by constructor <;> linarith⟩ 0 a r L K := by
    apply IsPicardLindelof.of_time_independent (a := a) (r := r) (L := L) (K := K)
      (fun y hy => (hB y hy).trans (le_max_left B 0)) hK
    have htime : max (t₀ + ε - t₀) (t₀ - (t₀ - ε)) = ε := by simp
    rw [htime]
    change (L : ℝ) * ε ≤ (R + 1) - R
    dsimp [ε]
    have hden : 0 < (L : ℝ) + 1 := by positivity
    rw [mul_one_div, div_le_iff₀ hden]
    nlinarith
  obtain ⟨α, hinit, hα⟩ := hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt
    (x := x) (by
      rw [mem_closedBall, dist_zero_right]
      change ‖x‖ ≤ R
      exact hx)
  exact ⟨α, hinit, fun t ht =>
    (hα t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)⟩

/-- Intersecting real convex sets have convex union. -/
theorem convex_union_real {I J : Set ℝ} (hI : Convex ℝ I) (hJ : Convex ℝ J)
    {s : ℝ} (hsI : s ∈ I) (hsJ : s ∈ J) : Convex ℝ (I ∪ J) := by
  rw [convex_iff_ordConnected]
  refine ⟨fun x hx y hy z hz => ?_⟩
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · exact Or.inl (hI.ordConnected.out hx hy hz)
  · by_cases hzs : z ≤ s
    · exact Or.inl (hI.ordConnected.out hx hsI ⟨hz.1, hzs⟩)
    · exact Or.inr (hJ.ordConnected.out hsJ hy ⟨le_of_not_ge hzs, hz.2⟩)
  · by_cases hzs : z ≤ s
    · exact Or.inr (hJ.ordConnected.out hx hsJ ⟨hz.1, hzs⟩)
    · exact Or.inl (hI.ordConnected.out hsI hy ⟨le_of_not_ge hzs, hz.2⟩)
  · exact Or.inr (hJ.ordConnected.out hx hy hz)

/-- Uniqueness makes the two solution germs agree on their whole overlap. -/
theorem normalized_solution_glue {I J : Set ℝ}
    (hI : Convex ℝ I) (hoI : IsOpen I) (hJ : Convex ℝ J) (hoJ : IsOpen J)
    {α β : ℝ → NormalizedState}
    (hα : ∀ t ∈ I, HasDerivAt α (normalizedField (α t)) t)
    (hβ : ∀ t ∈ J, HasDerivAt β (normalizedField (β t)) t)
    {s : ℝ} (hsI : s ∈ I) (hsJ : s ∈ J) (heq : α s = β s) :
    ∃ γ : ℝ → NormalizedState, EqOn γ α I ∧ EqOn γ β J ∧
      ∀ t ∈ I ∪ J, HasDerivAt γ (normalizedField (γ t)) t := by
  classical
  have hmatch := normalized_solution_unique (hI.inter hJ)
    (fun t ht => hα t ht.1) (fun t ht => hβ t ht.2) ⟨hsI, hsJ⟩ heq
  let γ : ℝ → NormalizedState := I.piecewise α β
  have heI : EqOn γ α I := fun t ht => piecewise_eq_of_mem I α β ht
  have heJ : EqOn γ β J := by
    intro t ht
    by_cases htI : t ∈ I
    · exact (heI htI).trans (hmatch ⟨htI, ht⟩)
    · exact piecewise_eq_of_notMem I α β htI
  refine ⟨γ, heI, heJ, fun t ht => ?_⟩
  rcases ht with ht | ht
  · rw [heI ht]
    exact (hα t ht).congr_of_eventuallyEq
      (Filter.eventuallyEq_of_mem (hoI.mem_nhds ht) fun u hu => heI hu)
  · rw [heJ ht]
    exact (hβ t ht).congr_of_eventuallyEq
      (Filter.eventuallyEq_of_mem (hoJ.mem_nhds ht) fun u hu => heJ hu)

end BianchiIX
