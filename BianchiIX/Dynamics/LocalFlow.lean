import BianchiIX.Dynamics.WallEvolution
import Mathlib.Analysis.ODE.ExistUnique

noncomputable section

namespace BianchiIX

open Set Filter Metric
open scoped Topology NNReal

theorem normalizedField_lipschitz_closedBall (x : NormalizedState) (r : ℝ) :
    ∃ L : ℝ≥0, LipschitzOnWith L normalizedField (closedBall x r) :=
  (contDiff_normalizedField 1).contDiffOn.exists_lipschitzOnWith (by norm_num)
    (convex_closedBall x r) (isCompact_closedBall x r)

theorem normalized_solution_unique_Icc {α β : ℝ → NormalizedState} {a b t₀ : ℝ}
    (hα : ∀ t ∈ Icc a b, HasDerivAt α (normalizedField (α t)) t)
    (hβ : ∀ t ∈ Icc a b, HasDerivAt β (normalizedField (β t)) t)
    (ht₀ : t₀ ∈ Icc a b) (heq : α t₀ = β t₀) : EqOn α β (Icc a b) := by
  have hcα := HasDerivAt.continuousOn hα
  have hcβ := HasDerivAt.continuousOn hβ
  obtain ⟨A, hA⟩ := isCompact_Icc.exists_bound_of_continuousOn hcα
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hcβ
  obtain ⟨L, hL⟩ := normalizedField_lipschitz_closedBall 0 (max A B)
  have hαball (t : ℝ) (ht : t ∈ Icc a b) : α t ∈ closedBall 0 (max A B) := by
    simpa only [mem_closedBall, dist_zero_right] using (hA t ht).trans (le_max_left A B)
  have hβball (t : ℝ) (ht : t ∈ Icc a b) : β t ∈ closedBall 0 (max A B) := by
    simpa only [mem_closedBall, dist_zero_right] using (hB t ht).trans (le_max_right A B)
  have hleft : Icc a t₀ ⊆ Icc a b := Icc_subset_Icc_right ht₀.2
  have hright : Icc t₀ b ⊆ Icc a b := Icc_subset_Icc_left ht₀.1
  rw [← Icc_union_Icc_eq_Icc ht₀.1 ht₀.2]
  apply EqOn.union
  · exact ODE_solution_unique_of_mem_Icc_left
      (v := fun _ => normalizedField) (s := fun _ => closedBall 0 (max A B))
      (fun _ _ => hL) (hcα.mono hleft)
      (fun t ht => (hα t (hleft (Ioc_subset_Icc_self ht))).hasDerivWithinAt)
      (fun t ht => hαball t (hleft (Ioc_subset_Icc_self ht))) (hcβ.mono hleft)
      (fun t ht => (hβ t (hleft (Ioc_subset_Icc_self ht))).hasDerivWithinAt)
      (fun t ht => hβball t (hleft (Ioc_subset_Icc_self ht))) heq
  · exact ODE_solution_unique_of_mem_Icc_right
      (v := fun _ => normalizedField) (s := fun _ => closedBall 0 (max A B))
      (fun _ _ => hL) (hcα.mono hright)
      (fun t ht => (hα t (hright (Ico_subset_Icc_self ht))).hasDerivWithinAt)
      (fun t ht => hαball t (hright (Ico_subset_Icc_self ht))) (hcβ.mono hright)
      (fun t ht => (hβ t (hright (Ico_subset_Icc_self ht))).hasDerivWithinAt)
      (fun t ht => hβball t (hright (Ico_subset_Icc_self ht))) heq

theorem normalized_solution_unique {I : Set ℝ} (hI : Convex ℝ I)
    {α β : ℝ → NormalizedState} {t₀ : ℝ}
    (hα : ∀ t ∈ I, HasDerivAt α (normalizedField (α t)) t)
    (hβ : ∀ t ∈ I, HasDerivAt β (normalizedField (β t)) t)
    (ht₀ : t₀ ∈ I) (heq : α t₀ = β t₀) : EqOn α β I := by
  intro t ht
  have hsub : uIcc t₀ t ⊆ I := hI.ordConnected.uIcc_subset ht₀ ht
  exact normalized_solution_unique_Icc (fun u hu => hα u (hsub hu))
    (fun u hu => hβ u (hsub hu)) left_mem_uIcc heq right_mem_uIcc

/-- The composition law is asserted only where both local solutions are defined. -/
theorem normalized_localFlow_add {x₀ : NormalizedState} {r ε : ℝ} (hε : 0 < ε)
    {Φ : NormalizedState × ℝ → NormalizedState}
    (hinit : ∀ x ∈ closedBall x₀ r, Φ (x, 0) = x)
    (hΦ : ∀ x ∈ closedBall x₀ r, ∀ t ∈ Ioo (-ε) ε,
      HasDerivAt (fun u => Φ (x, u)) (normalizedField (Φ (x, t))) t)
    {x : NormalizedState} {s t : ℝ} (hx : x ∈ closedBall x₀ r)
    (hs : s ∈ Ioo (-ε) ε) (ht : t ∈ Ioo (-ε) ε) (hst : s + t ∈ Ioo (-ε) ε)
    (hy : Φ (x, s) ∈ closedBall x₀ r) : Φ (Φ (x, s), t) = Φ (x, s + t) := by
  let I : Set ℝ := Ioo (-ε) ε ∩ Ioo (-ε - s) (ε - s)
  have hI : Convex ℝ I := (convex_Ioo _ _).inter (convex_Ioo _ _)
  have hzero : (0 : ℝ) ∈ I := by
    refine ⟨⟨by linarith, hε⟩, ?_⟩
    constructor <;> linarith [hs.1, hs.2]
  have htI : t ∈ I := by
    refine ⟨ht, ?_⟩
    constructor <;> linarith [hst.1, hst.2]
  have hshift (u : ℝ) (hu : u ∈ I) :
      HasDerivAt (fun v => Φ (x, s + v)) (normalizedField (Φ (x, s + u))) u := by
    have hsu : s + u ∈ Ioo (-ε) ε := by
      constructor <;> linarith [hu.2.1, hu.2.2]
    convert! (hΦ x hx (s + u) hsu).scomp u ((hasDerivAt_id u).const_add s) using 1
    simp
  exact normalized_solution_unique hI (fun u hu => hΦ _ hy u hu.1) hshift hzero
    (by simpa using hinit _ hy) htI

/-- A jointly continuous family on one common space-time neighbourhood. -/
theorem exists_normalized_localFlow (x₀ : NormalizedState) (t₀ : ℝ) :
    ∃ r > (0 : ℝ), ∃ ε > (0 : ℝ), ∃ Φ : NormalizedState × ℝ → NormalizedState,
      ContinuousOn Φ (closedBall x₀ r ×ˢ Icc (t₀ - ε) (t₀ + ε)) ∧
      ∀ x ∈ closedBall x₀ r, Φ (x, t₀) = x ∧
        ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε),
          HasDerivAt (fun u => Φ (x, u)) (normalizedField (Φ (x, t))) t ∧
          stateConstraint (Φ (x, t)) = stateConstraint x := by
  obtain ⟨ε, hε, a, r, L, K, hr, hPL⟩ :=
    IsPicardLindelof.of_contDiffAt_one ((contDiff_normalizedField 1).contDiffAt (x := x₀))
  obtain ⟨Φ, hΦ, hcΦ⟩ := (hPL t₀).exists_forall_mem_closedBall_eq_hasDerivWithinAt_continuousOn
  refine ⟨r, hr, ε, hε, Φ, hcΦ, ?_⟩
  intro x hx
  have hODE (t : ℝ) (ht : t ∈ Ioo (t₀ - ε) (t₀ + ε)) :
      HasDerivAt (fun u => Φ (x, u)) (normalizedField (Φ (x, t))) t :=
    ((hΦ x hx).2 t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  refine ⟨(hΦ x hx).1, fun t ht => ⟨hODE t ht, ?_⟩⟩
  have ht₀ : t₀ ∈ Ioo (t₀ - ε) (t₀ + ε) := by constructor <;> linarith
  exact (normalized_constraint_constant (convex_Ioo _ _) hODE ht₀ ht).trans
    (congrArg stateConstraint (hΦ x hx).1)

theorem exists_normalized_solution (x₀ : NormalizedState) (t₀ : ℝ) :
    ∃ α : ℝ → NormalizedState, α t₀ = x₀ ∧ ∃ ε > (0 : ℝ),
      ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε),
        HasDerivAt α (normalizedField (α t)) t ∧ stateConstraint (α t) = stateConstraint x₀ := by
  obtain ⟨r, hr, ε, hε, Φ, _, hΦ⟩ := exists_normalized_localFlow x₀ t₀
  exact ⟨fun t => Φ (x₀, t), (hΦ x₀ (mem_closedBall_self hr.le)).1,
    ε, hε, (hΦ x₀ (mem_closedBall_self hr.le)).2⟩

theorem exists_normalized_physical_solution {x₀ : NormalizedState}
    (hpos : positiveWalls x₀) (hconstraint : stateConstraint x₀ = 1) (t₀ : ℝ) :
    ∃ ε > (0 : ℝ), ∃ α : ℝ → NormalizedState, α t₀ = x₀ ∧
      ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε),
        HasDerivAt α (normalizedField (α t)) t ∧ positiveWalls (α t) ∧ stateConstraint (α t) = 1 := by
  obtain ⟨α, hinit, ε, hε, hα⟩ := exists_normalized_solution x₀ t₀
  have ht₀ : t₀ ∈ Ioo (t₀ - ε) (t₀ + ε) := by constructor <;> linarith
  refine ⟨ε, hε, α, hinit, fun t ht => ?_⟩
  exact ⟨(hα t ht).1, normalized_positive_walls_invariant (convex_Ioo _ _) isOpen_Ioo
    (fun u hu => (hα u hu).1) ht₀ ht (hinit ▸ hpos), ((hα t ht).2).trans hconstraint⟩

end BianchiIX
