import BianchiIX.Dynamics.InitialDerivative

noncomputable section

namespace BianchiIX

open Set Filter Metric Asymptotics
open scoped Topology NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem ode_norm_le_gronwall_uIcc {f df : ℝ → E} {t₀ t δ K ε : ℝ}
    (hf : ∀ u ∈ uIcc t₀ t, HasDerivAt f (df u) u) (hinit : ‖f t₀‖ ≤ δ)
    (hbound : ∀ u ∈ uIcc t₀ t, ‖df u‖ ≤ K * ‖f u‖ + ε) :
    ‖f t‖ ≤ gronwallBound δ K ε |t - t₀| := by
  by_cases htt : t₀ ≤ t
  · rw [uIcc_of_le htt] at hf hbound
    simpa only [abs_of_nonneg (sub_nonneg.mpr htt)] using
      norm_le_gronwallBound_of_norm_deriv_right_le (HasDerivAt.continuousOn hf)
        (fun u hu => (hf u (Ico_subset_Icc_self hu)).hasDerivWithinAt) hinit
        (fun u hu => hbound u (Ico_subset_Icc_self hu)) t ⟨htt, le_rfl⟩
  · have hrev (u : ℝ) (hu : u ∈ Icc 0 (t₀ - t)) : t₀ - u ∈ uIcc t₀ t := by
      rw [uIcc_of_ge (le_of_not_ge htt)]
      constructor <;> linarith [hu.1, hu.2]
    have hg (u : ℝ) (hu : u ∈ Icc 0 (t₀ - t)) :
        HasDerivAt (fun v => f (t₀ - v)) (-df (t₀ - u)) u := by
      convert! (hf (t₀ - u) (hrev u hu)).scomp u ((hasDerivAt_id u).const_sub t₀) using 1
      simp
    have H := norm_le_gronwallBound_of_norm_deriv_right_le (HasDerivAt.continuousOn hg)
      (fun u hu => (hg u (Ico_subset_Icc_self hu)).hasDerivWithinAt)
      (δ := δ) (K := K) (ε := ε) (by simpa using hinit)
      (fun u hu => by simpa using hbound (t₀ - u) (hrev u (Ico_subset_Icc_self hu)))
      (t₀ - t) ⟨by linarith, le_rfl⟩
    simpa [abs_of_neg (sub_neg.mpr (lt_of_not_ge htt)), neg_sub] using H

theorem ode_quadratic_remainder {f : E → E} {D : E → E →L[ℝ] E}
    (hf : ∀ x, HasFDerivAt f (D x) x) {S : Set E} (hS : Convex ℝ S)
    {K : ℝ≥0} (hK : LipschitzOnWith K D S) {x y : E} (hx : x ∈ S) (hy : y ∈ S) :
    ‖f y - f x - D x (y - x)‖ ≤ K * ‖y - x‖ ^ 2 := by
  let g : E → E := fun z => f z - D x z
  have hg (z : E) : HasFDerivAt g (D z - D x) z := (hf z).sub (D x).hasFDerivAt
  have hbound (z : E) (hz : z ∈ segment ℝ x y) : ‖D z - D x‖ ≤ K * ‖y - x‖ :=
    (hK.norm_sub_le (hS.segment_subset hx hy hz) hx).trans
      (mul_le_mul_of_nonneg_left (norm_sub_le_of_mem_segment hz) K.coe_nonneg)
  have H := (convex_segment x y).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun z _ => (hg z).hasFDerivWithinAt) hbound (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
  simpa only [g, map_sub, sub_sub_sub_comm, pow_two, mul_assoc] using H

/-- The variational equation controls the actual nonlinear remainder in any state space. -/
theorem ode_variation_remainder {f : E → E} {D : E → E →L[ℝ] E}
    (hf : ∀ x, HasFDerivAt f (D x) x) {α β : ℝ → E} {J : ℝ → E →L[ℝ] E}
    {t₀ t : ℝ} {S : Set E} (hS : Convex ℝ S) {K L : ℝ} {C : ℝ≥0}
    (hD : LipschitzOnWith C D S)
    (hα : ∀ u ∈ uIcc t₀ t, HasDerivAt α (f (α u)) u)
    (hβ : ∀ u ∈ uIcc t₀ t, HasDerivAt β (f (β u)) u)
    (hαS : ∀ u ∈ uIcc t₀ t, α u ∈ S) (hβS : ∀ u ∈ uIcc t₀ t, β u ∈ S)
    (hJ : ∀ u ∈ uIcc t₀ t, HasDerivAt J ((D (α u)).comp (J u)) u)
    (hJinit : J t₀ = ContinuousLinearMap.id ℝ E)
    (hDnorm : ∀ u ∈ uIcc t₀ t, ‖D (α u)‖ ≤ K)
    (hclose : ∀ u ∈ uIcc t₀ t, ‖β u - α u‖ ≤ L * ‖β t₀ - α t₀‖) :
    ‖β t - α t - J t (β t₀ - α t₀)‖ ≤
      gronwallBound 0 K (C * L ^ 2) |t - t₀| * ‖β t₀ - α t₀‖ ^ 2 := by
  let h := β t₀ - α t₀
  let e := fun u => β u - α u - J u h
  let de := fun u => f (β u) - f (α u) - D (α u) (J u h)
  have he (u : ℝ) (hu : u ∈ uIcc t₀ t) : HasDerivAt e (de u) u := by
    convert! ((hβ u hu).sub (hα u hu)).sub ((hJ u hu).clm_apply (hasDerivAt_const u h)) using 1
    simp [de]
  have hb (u : ℝ) (hu : u ∈ uIcc t₀ t) : ‖de u‖ ≤ K * ‖e u‖ + C * L ^ 2 * ‖h‖ ^ 2 := by
    have hde : de u = D (α u) (e u) + (f (β u) - f (α u) - D (α u) (β u - α u)) := by
      simp only [de, e, map_sub]
      abel
    rw [hde]
    apply (norm_add_le _ _).trans
    apply add_le_add
    · exact ((D (α u)).le_opNorm (e u)).trans
        (mul_le_mul_of_nonneg_right (hDnorm u hu) (norm_nonneg _))
    · apply (ode_quadratic_remainder hf hS hD (hαS u hu) (hβS u hu)).trans
      calc
        (C : ℝ) * ‖β u - α u‖ ^ 2 ≤ C * (L * ‖h‖) ^ 2 := by gcongr; exact hclose u hu
        _ = C * L ^ 2 * ‖h‖ ^ 2 := by ring
  have H := ode_norm_le_gronwall_uIcc he (δ := 0) (by simp [e, h, hJinit]) hb
  have hscale : gronwallBound 0 K (C * L ^ 2 * ‖h‖ ^ 2) |t - t₀| =
      gronwallBound 0 K (C * L ^ 2) |t - t₀| * ‖h‖ ^ 2 := by
    unfold gronwallBound
    split_ifs <;> ring
  simpa only [hscale, e, h] using H

/-- Uniqueness for a continuous linear equation on either orientation of a time interval. -/
theorem ode_linear_solution_unique {A : ℝ → E →L[ℝ] E} {α β : ℝ → E} {t₀ t : ℝ}
    (hA : ContinuousOn A (uIcc t₀ t))
    (hα : ∀ u ∈ uIcc t₀ t, HasDerivAt α (A u (α u)) u)
    (hβ : ∀ u ∈ uIcc t₀ t, HasDerivAt β (A u (β u)) u)
    (hinit : α t₀ = β t₀) : α t = β t := by
  obtain ⟨K, hK⟩ := isCompact_uIcc.exists_bound_of_continuousOn hA
  have H := ode_norm_le_gronwall_uIcc (fun u hu => (hα u hu).sub (hβ u hu))
    (δ := 0) (ε := 0) (by simp [hinit]) (fun u hu => by
      rw [← map_sub, add_zero]
      exact ((A u).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hK u hu) (norm_nonneg _)))
  have hzero : gronwallBound 0 K 0 |t - t₀| = 0 := by unfold gronwallBound; split_ifs <;> simp
  rw [hzero] at H
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm H (norm_nonneg _)))

end BianchiIX
