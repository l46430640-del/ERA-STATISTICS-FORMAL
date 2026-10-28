import BianchiIX.Dynamics.ForwardComplete

noncomputable section

namespace BianchiIX

open Set MeasureTheory

/-- The exponential wall formula preserves both zero walls and their signs. -/
theorem normalized_wall_sign {I : Set ℝ} (hI : Convex ℝ I) (ho : IsOpen I)
    {α : ℝ → NormalizedState} (hα : ∀ t ∈ I, HasDerivAt α (normalizedField (α t)) t)
    {s t : ℝ} (hs : s ∈ I) (ht : t ∈ I) (i : Fin 3) :
    (wallValue i (α t) = 0 ↔ wallValue i (α s) = 0) ∧
      (0 ≤ wallValue i (α t) ↔ 0 ≤ wallValue i (α s)) := by
  rw [normalized_wall_formula hI ho hα hs ht i]
  exact ⟨mul_eq_zero.trans (or_iff_left (Real.exp_ne_zero _)),
    mul_nonneg_iff_of_pos_right (Real.exp_pos _)⟩

theorem normalized_wall_abs_growth {I : Set ℝ} (hI : Convex ℝ I) (ho : IsOpen I)
    {α : ℝ → NormalizedState} (hα : ∀ t ∈ I, HasDerivAt α (normalizedField (α t)) t)
    {s t : ℝ} (hs : s ∈ I) (ht : t ∈ I) (hst : s ≤ t) (i : Fin 3) :
    |wallValue i (α t)| ≤ |wallValue i (α s)| * Real.exp (t - s) := by
  have hc := (continuous_wallRate i).comp_continuousOn (HasDerivAt.continuousOn hα)
  have hi : IntervalIntegrable (fun u => wallRate i (α u)) volume s t :=
    (hc.mono (hI.ordConnected.uIcc_subset hs ht)).intervalIntegrable
  have H : (∫ u in s..t, wallRate i (α u)) ≤ t - s := by
    have H := intervalIntegral.integral_mono_on hst hi (intervalIntegrable_const (c := (1 : ℝ)))
      (fun u _ => wallRate_le_one i (α u))
    simpa using H
  rw [normalized_wall_formula hI ho hα hs ht i, abs_mul, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr H) (abs_nonneg _)

/-- The constraint controls the shear using absolute wall bounds; positivity is unnecessary. -/
theorem normalizedState_norm_bound_abs {x : NormalizedState} {M : ℝ}
    (hcon : stateConstraint x = 1) (hwall : ∀ i : Fin 3, |wallValue i x| ≤ M) :
    ‖x‖ ≤ 1 + 3 * M := by
  have h₂ : |x 2| ≤ M := hwall 0
  have h₃ : |x 3| ≤ M := hwall 1
  have h₄ : |x 4| ≤ M := hwall 2
  have hM : 0 ≤ M := (abs_nonneg _).trans h₂
  have hsum : |x 2 + x 3 + x 4| ≤ 3 * M := by
    calc
      _ ≤ |x 2 + x 3| + |x 4| := abs_add_le _ _
      _ ≤ |x 2| + |x 3| + |x 4| := add_le_add (abs_add_le _ _) le_rfl
      _ ≤ 3 * M := by linarith
  have hsum2 : (x 2 + x 3 + x 4) ^ 2 ≤ (3 * M) ^ 2 :=
    sq_le_sq.mpr (by simpa only [abs_of_nonneg (by positivity : 0 ≤ 3 * M)] using hsum)
  have hconstraint : x 0 ^ 2 + x 1 ^ 2 + curvature (x 2) (x 3) (x 4) = 1 := hcon
  unfold curvature at hconstraint
  have hS : x 0 ^ 2 + x 1 ^ 2 ≤ 1 + 9 * M ^ 2 := by
    nlinarith [sq_nonneg (x 2), sq_nonneg (x 3), sq_nonneg (x 4)]
  have hR : 0 ≤ 1 + 3 * M := by positivity
  have hp : |x 0| ≤ 1 + 3 * M := by
    apply (sq_le_sq₀ (abs_nonneg _) hR).mp
    rw [sq_abs]
    nlinarith [sq_nonneg (x 1)]
  have hs : |x 1| ≤ 1 + 3 * M := by
    apply (sq_le_sq₀ (abs_nonneg _) hR).mp
    rw [sq_abs]
    nlinarith [sq_nonneg (x 0)]
  apply (pi_norm_le_iff_of_nonneg hR).mpr
  intro i
  fin_cases i
  · exact hp
  · exact hs
  · change |x 2| ≤ 1 + 3 * M
    linarith
  · change |x 3| ≤ 1 + 3 * M
    linarith
  · change |x 4| ≤ 1 + 3 * M
    linarith

theorem NormalizedSolution.forward_bound_of_constraint {x₀ : NormalizedState} {t₀ : ℝ}
    (S : NormalizedSolution x₀ t₀) (hcon : stateConstraint x₀ = 1)
    {t : ℝ} (ht : t ∈ S.domain) (htt : t₀ ≤ t) :
    ‖S.curve t‖ ≤ 1 + 3 * ‖x₀‖ * Real.exp (t - t₀) := by
  have hc : stateConstraint (S.curve t) = 1 :=
    (normalized_constraint_constant S.convex_domain S.hasDerivAt S.initial_mem ht).trans
      ((congrArg stateConstraint S.initial_eq).trans hcon)
  have H := normalizedState_norm_bound_abs hc (fun i =>
    (normalized_wall_abs_growth S.convex_domain S.isOpen_domain S.hasDerivAt S.initial_mem ht htt i).trans
      (mul_le_mul_of_nonneg_right
        (show |wallValue i (S.curve t₀)| ≤ ‖x₀‖ by
          rw [S.initial_eq]
          exact norm_le_pi_norm x₀ (i.addNat 2)) (Real.exp_pos _).le))
  simpa only [mul_assoc] using H

/-- Every constraint-one initial state is forward complete, including all zero-wall faces. -/
theorem normalizedMaxDomain_contains_Ici_of_constraint {x₀ : NormalizedState}
    (hcon : stateConstraint x₀ = 1) (t₀ : ℝ) :
    Ici t₀ ⊆ normalizedMaxDomain x₀ t₀ := by
  apply normalizedMaxDomain_forward_of_bounds
  intro T
  refine ⟨1 + 3 * ‖x₀‖ * Real.exp (T - t₀), by positivity, fun t ht htt => ?_⟩
  apply ((maximalNormalizedSolution x₀ t₀).forward_bound_of_constraint hcon ht htt.1).trans
  gcongr
  exact htt.2

theorem normalizedMaxCurve_forward_of_constraint {x₀ : NormalizedState}
    (hcon : stateConstraint x₀ = 1) {t₀ t : ℝ} (htt : t₀ ≤ t) :
    HasDerivAt (normalizedMaxCurve x₀ t₀) (normalizedField (normalizedMaxCurve x₀ t₀ t)) t ∧
      stateConstraint (normalizedMaxCurve x₀ t₀ t) = 1 ∧
      ‖normalizedMaxCurve x₀ t₀ t‖ ≤ 1 + 3 * ‖x₀‖ * Real.exp (t - t₀) := by
  let S := maximalNormalizedSolution x₀ t₀
  have ht : t ∈ S.domain := normalizedMaxDomain_contains_Ici_of_constraint hcon t₀ htt
  exact ⟨S.hasDerivAt t ht,
    (normalized_constraint_constant S.convex_domain S.hasDerivAt S.initial_mem ht).trans
      ((congrArg stateConstraint S.initial_eq).trans hcon),
    S.forward_bound_of_constraint hcon ht htt⟩

theorem normalizedMaxCurve_wall_sign {x₀ : NormalizedState}
    (hcon : stateConstraint x₀ = 1) {t₀ t : ℝ} (htt : t₀ ≤ t) (i : Fin 3) :
    (wallValue i (normalizedMaxCurve x₀ t₀ t) = 0 ↔ wallValue i x₀ = 0) ∧
      (0 ≤ wallValue i (normalizedMaxCurve x₀ t₀ t) ↔ 0 ≤ wallValue i x₀) := by
  let S := maximalNormalizedSolution x₀ t₀
  have ht : t ∈ S.domain := normalizedMaxDomain_contains_Ici_of_constraint hcon t₀ htt
  have H := normalized_wall_sign S.convex_domain S.isOpen_domain S.hasDerivAt S.initial_mem ht i
  rw [S.initial_eq] at H
  convert! H using 1

end BianchiIX
