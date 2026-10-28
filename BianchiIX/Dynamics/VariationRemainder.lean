import BianchiIX.Dynamics.Variational

noncomputable section

namespace BianchiIX

open Set Filter Metric
open scoped Topology NNReal

theorem norm_le_gronwall_uIcc {f df : ℝ → NormalizedState} {t₀ t δ K ε : ℝ}
    (hf : ∀ u ∈ uIcc t₀ t, HasDerivAt f (df u) u)
    (hinit : ‖f t₀‖ ≤ δ)
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

/-- The actual solution error satisfies a quadratic bound once the linear variational equation holds. -/
theorem normalized_variation_remainder {α β : ℝ → NormalizedState}
    {J : ℝ → NormalizedVariation} {t₀ t : ℝ} {S : Set NormalizedState}
    (hS : Convex ℝ S) {K L : ℝ} {C : ℝ≥0}
    (hD : LipschitzOnWith C normalizedDifferential S)
    (hα : ∀ u ∈ uIcc t₀ t, HasDerivAt α (normalizedField (α u)) u)
    (hβ : ∀ u ∈ uIcc t₀ t, HasDerivAt β (normalizedField (β u)) u)
    (hαS : ∀ u ∈ uIcc t₀ t, α u ∈ S) (hβS : ∀ u ∈ uIcc t₀ t, β u ∈ S)
    (hJ : ∀ u ∈ uIcc t₀ t, HasDerivAt J ((normalizedDifferential (α u)).comp (J u)) u)
    (hJinit : J t₀ = ContinuousLinearMap.id ℝ NormalizedState)
    (hDnorm : ∀ u ∈ uIcc t₀ t, ‖normalizedDifferential (α u)‖ ≤ K)
    (hclose : ∀ u ∈ uIcc t₀ t, ‖β u - α u‖ ≤ L * ‖β t₀ - α t₀‖) :
    ‖β t - α t - J t (β t₀ - α t₀)‖ ≤
      gronwallBound 0 K (C * L ^ 2) |t - t₀| * ‖β t₀ - α t₀‖ ^ 2 := by
  let h := β t₀ - α t₀
  let e := fun u => β u - α u - J u h
  let de := fun u => normalizedField (β u) - normalizedField (α u) -
    normalizedDifferential (α u) (J u h)
  have he (u : ℝ) (hu : u ∈ uIcc t₀ t) : HasDerivAt e (de u) u := by
    have hJh := (hJ u hu).clm_apply (hasDerivAt_const u h)
    convert! ((hβ u hu).sub (hα u hu)).sub hJh using 1
    simp [de]
  have hb (u : ℝ) (hu : u ∈ uIcc t₀ t) :
      ‖de u‖ ≤ K * ‖e u‖ + C * L ^ 2 * ‖h‖ ^ 2 := by
    have hde : de u = normalizedDifferential (α u) (e u) +
        (normalizedField (β u) - normalizedField (α u) -
          normalizedDifferential (α u) (β u - α u)) := by
      simp only [de, e, map_sub]
      abel
    rw [hde]
    apply (norm_add_le _ _).trans
    apply add_le_add
    · exact ((normalizedDifferential (α u)).le_opNorm (e u)).trans
        (mul_le_mul_of_nonneg_right (hDnorm u hu) (norm_nonneg _))
    · apply (normalizedField_quadratic_remainder hS hD (hαS u hu) (hβS u hu)).trans
      calc
        (C : ℝ) * ‖β u - α u‖ ^ 2 ≤ C * (L * ‖h‖) ^ 2 := by
          gcongr
          exact hclose u hu
        _ = C * L ^ 2 * ‖h‖ ^ 2 := by ring
  have H := norm_le_gronwall_uIcc he (δ := 0) (by simp [e, h, hJinit]) hb
  have hscale : gronwallBound 0 K (C * L ^ 2 * ‖h‖ ^ 2) |t - t₀| =
      gronwallBound 0 K (C * L ^ 2) |t - t₀| * ‖h‖ ^ 2 := by
    unfold gronwallBound
    split_ifs <;> ring
  simpa only [hscale, e, h] using H

end BianchiIX
