import BianchiIX.Dynamics.MaximalFlow

noncomputable section

namespace BianchiIX

open Set Filter Metric
open scoped Topology

private theorem lt_csSup_of_mem_open {I : Set ℝ} (ho : IsOpen I) (hb : BddAbove I)
    {t : ℝ} (ht : t ∈ I) : t < sSup I := by
  obtain ⟨l, u, htu, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp (ho.mem_nhds ht)
  have hmid : (t + u) / 2 ∈ I := hsub ⟨by linarith [htu.1, htu.2], by linarith [htu.2]⟩
  exact (show t < (t + u) / 2 by linarith [htu.2]).trans_le (le_csSup hb hmid)

/-- Bounds on each finite forward interval exclude a finite maximal right endpoint. -/
theorem normalizedMaxDomain_forward_of_bounds {x₀ : NormalizedState} {t₀ : ℝ}
    (hbound : ∀ T : ℝ, ∃ R ≥ (0 : ℝ), ∀ t ∈ normalizedMaxDomain x₀ t₀,
      t ∈ Icc t₀ T → ‖normalizedMaxCurve x₀ t₀ t‖ ≤ R) :
    Ici t₀ ⊆ normalizedMaxDomain x₀ t₀ := by
  let S := maximalNormalizedSolution x₀ t₀
  have hunbounded : ¬ BddAbove S.domain := by
    intro hb
    let b := sSup S.domain
    have ht₀b : t₀ < b := lt_csSup_of_mem_open S.isOpen_domain hb S.initial_mem
    obtain ⟨R, hR, hboundR⟩ := hbound b
    obtain ⟨ε, hε, hlocal⟩ := exists_normalized_solution_uniform R hR
    have hmax : max t₀ (b - ε) < b := max_lt ht₀b (by linarith)
    obtain ⟨s, hs, hclose⟩ := exists_lt_of_lt_csSup ⟨t₀, S.initial_mem⟩ hmax
    have hsbound := hboundR s hs ⟨(le_max_left _ _).trans hclose.le, le_csSup hb hs⟩
    obtain ⟨β, hinit, hβ⟩ := hlocal (S.curve s) hsbound s
    have hsJ : s ∈ Ioo (s - ε) (s + ε) := by constructor <;> linarith
    have hbJ : b ∈ Ioo (s - ε) (s + ε) := by
      have hsb : s ≤ b := le_csSup hb hs
      have hbs : b - ε < s := (le_max_right _ _).trans_lt hclose
      constructor <;> linarith
    have hbmem := normalizedMaxDomain_contains_extension (convex_Ioo _ _) isOpen_Ioo
      hβ hs hsJ hinit.symm hbJ
    exact (lt_irrefl b) (lt_csSup_of_mem_open S.isOpen_domain hb hbmem)
  intro t ht
  obtain ⟨u, hu, htu⟩ := not_bddAbove_iff.mp hunbounded t
  exact S.convex_domain.ordConnected.out S.initial_mem hu ⟨ht, htu.le⟩

theorem NormalizedSolution.physical {x₀ : NormalizedState} {t₀ : ℝ}
    (S : NormalizedSolution x₀ t₀) (hpos : positiveWalls x₀) (hcon : stateConstraint x₀ = 1)
    {t : ℝ} (ht : t ∈ S.domain) :
    positiveWalls (S.curve t) ∧ stateConstraint (S.curve t) = 1 := by
  refine ⟨normalized_positive_walls_invariant S.convex_domain S.isOpen_domain S.hasDerivAt
    S.initial_mem ht (by rw [S.initial_eq]; exact hpos), ?_⟩
  exact (normalized_constraint_constant S.convex_domain S.hasDerivAt S.initial_mem ht).trans
    ((congrArg stateConstraint S.initial_eq).trans hcon)

theorem NormalizedSolution.forward_bound {x₀ : NormalizedState} {t₀ : ℝ}
    (S : NormalizedSolution x₀ t₀) (hpos : positiveWalls x₀) (hcon : stateConstraint x₀ = 1)
    {t : ℝ} (ht : t ∈ S.domain) (htt : t₀ ≤ t) :
    ‖S.curve t‖ ≤ 1 + 3 * ‖x₀‖ * Real.exp (t - t₀) := by
  apply normalized_forward_bound S.convex_domain S.isOpen_domain S.hasDerivAt
    S.initial_mem ht htt (by rw [S.initial_eq]; exact hpos) (by rw [S.initial_eq]; exact hcon)
  intro i
  rw [S.initial_eq]
  exact (le_abs_self _).trans (norm_le_pi_norm x₀ (i.addNat 2))

/-- Physical initial data for the exact normalized Einstein ODE are forward complete. -/
theorem normalizedMaxDomain_contains_Ici {x₀ : NormalizedState}
    (hpos : positiveWalls x₀) (hcon : stateConstraint x₀ = 1) (t₀ : ℝ) :
    Ici t₀ ⊆ normalizedMaxDomain x₀ t₀ := by
  apply normalizedMaxDomain_forward_of_bounds
  intro T
  refine ⟨1 + 3 * ‖x₀‖ * Real.exp (T - t₀), by positivity, fun t ht htt => ?_⟩
  apply ((maximalNormalizedSolution x₀ t₀).forward_bound hpos hcon ht htt.1).trans
  gcongr
  exact htt.2

theorem normalizedMaxCurve_forward {x₀ : NormalizedState}
    (hpos : positiveWalls x₀) (hcon : stateConstraint x₀ = 1) {t₀ t : ℝ} (htt : t₀ ≤ t) :
    HasDerivAt (normalizedMaxCurve x₀ t₀) (normalizedField (normalizedMaxCurve x₀ t₀ t)) t ∧
      positiveWalls (normalizedMaxCurve x₀ t₀ t) ∧
      stateConstraint (normalizedMaxCurve x₀ t₀ t) = 1 ∧
      ‖normalizedMaxCurve x₀ t₀ t‖ ≤ 1 + 3 * ‖x₀‖ * Real.exp (t - t₀) := by
  let S := maximalNormalizedSolution x₀ t₀
  have ht : t ∈ S.domain := normalizedMaxDomain_contains_Ici hpos hcon t₀ htt
  have hp := S.physical hpos hcon ht
  exact ⟨S.hasDerivAt t ht, hp.1, hp.2, S.forward_bound hpos hcon ht htt⟩

theorem exists_normalized_forward_solution {x₀ : NormalizedState}
    (hpos : positiveWalls x₀) (hcon : stateConstraint x₀ = 1) (t₀ : ℝ) :
    ∃ α : ℝ → NormalizedState, α t₀ = x₀ ∧ ∀ t ≥ t₀,
      HasDerivAt α (normalizedField (α t)) t ∧ positiveWalls (α t) ∧
        stateConstraint (α t) = 1 ∧ ‖α t‖ ≤ 1 + 3 * ‖x₀‖ * Real.exp (t - t₀) :=
  ⟨normalizedMaxCurve x₀ t₀, normalizedMaxCurve_initial x₀ t₀,
    fun _ ht => normalizedMaxCurve_forward hpos hcon ht⟩

theorem normalized_forwardFlow_add {x₀ : NormalizedState}
    (hpos : positiveWalls x₀) (hcon : stateConstraint x₀ = 1)
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    normalizedMaxCurve (normalizedMaxCurve x₀ 0 s) 0 t = normalizedMaxCurve x₀ 0 (s + t) := by
  have hstate := normalizedMaxCurve_forward hpos hcon hs
  have hshift (u : ℝ) (hu : u ∈ Ici (0 : ℝ)) :
      HasDerivAt (fun v => normalizedMaxCurve x₀ 0 (s + v))
        (normalizedField (normalizedMaxCurve x₀ 0 (s + u))) u := by
    convert! (normalizedMaxCurve_forward hpos hcon (add_nonneg hs hu)).1.scomp u
      ((hasDerivAt_id u).const_add s) using 1
    simp
  exact normalized_solution_unique (t₀ := (0 : ℝ)) (convex_Ici 0)
    (fun _ hu => (normalizedMaxCurve_forward hstate.2.1 hstate.2.2.1 hu).1)
    hshift (by simp) (by simp [normalizedMaxCurve_initial]) ht

end BianchiIX
