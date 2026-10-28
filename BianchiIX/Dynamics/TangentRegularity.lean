import BianchiIX.Analysis.ODELocalFlow
import BianchiIX.Dynamics.FlowDifferential

noncomputable section

namespace BianchiIX

open Set Filter Metric
open scoped Topology

/-- Smooth dependence for the tangent equation, identified with the exact maximal state flow. -/
theorem exists_normalized_variation_family_contDiff_one (x₀ : NormalizedState) (t₀ : ℝ) :
    ∃ r > (0 : ℝ), ∃ ε > (0 : ℝ), ∃ J : NormalizedState × ℝ → NormalizedVariation,
      ContDiffOn ℝ 1 J (ball x₀ r ×ˢ Ioo (t₀ - ε) (t₀ + ε)) ∧
      ∀ x ∈ ball x₀ r, Ioo (t₀ - ε) (t₀ + ε) ⊆ normalizedMaxDomain x t₀ ∧
        J (x, t₀) = ContinuousLinearMap.id ℝ NormalizedState ∧
        ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε),
          HasDerivAt (fun u => J (x, u))
            ((normalizedDifferential (normalizedMaxCurve x t₀ t)).comp (J (x, t))) t := by
  let idE := ContinuousLinearMap.id ℝ NormalizedState
  obtain ⟨r, hr, ε, hε, Φ, hcΦ, hΦ⟩ :=
    exists_ode_local_contDiff_one (contDiff_normalizedTangentField 2) (x₀, idE) t₀
  have hxpair (x : NormalizedState) (hx : x ∈ ball x₀ r) : (x, idE) ∈ ball (x₀, idE) r := by
    simpa only [mem_ball, dist_prod_same_right] using hx
  have hode (x : NormalizedState) (hx : x ∈ ball x₀ r)
      (t : ℝ) (ht : t ∈ Ioo (t₀ - ε) (t₀ + ε)) :=
    hasDerivAt_normalizedTangent_components ((hΦ (x, idE) (hxpair x hx)).2 t ht)
  have ht₀ : t₀ ∈ Ioo (t₀ - ε) (t₀ + ε) := by constructor <;> linarith
  let S (x : NormalizedState) (hx : x ∈ ball x₀ r) : NormalizedSolution x t₀ :=
    ⟨Ioo (t₀ - ε) (t₀ + ε), isOpen_Ioo, convex_Ioo _ _, ht₀,
      fun t => (Φ ((x, idE), t)).1,
      congrArg Prod.fst (hΦ (x, idE) (hxpair x hx)).1,
      fun t ht => (hode x hx t ht).1⟩
  let J : NormalizedState × ℝ → NormalizedVariation := fun z => (Φ ((z.1, idE), z.2)).2
  refine ⟨r, hr, ε, hε, J, ?_, fun x hx => ?_⟩
  · apply contDiff_snd.comp_contDiffOn
    exact hcΦ.comp (by fun_prop : ContDiffOn ℝ 1
      (fun z : NormalizedState × ℝ => ((z.1, idE), z.2)) _)
      (fun z hz => ⟨hxpair z.1 hz.1, hz.2⟩)
  · refine ⟨(S x hx).domain_subset_maximal, congrArg Prod.snd (hΦ (x, idE) (hxpair x hx)).1, ?_⟩
    intro t ht
    rw [normalizedMaxCurve_eqOn (S x hx) ht]
    exact (hode x hx t ht).2

/-- A differentiable tangent flow gives two derivatives of the original exact flow. -/
theorem exists_normalizedMaxCurve_local_contDiff_two (x₀ : NormalizedState) (t₀ : ℝ) :
    ∃ r > (0 : ℝ), ∃ ε > (0 : ℝ),
      (∀ x ∈ ball x₀ r, Ioo (t₀ - ε) (t₀ + ε) ⊆ normalizedMaxDomain x t₀) ∧
      ContDiffOn ℝ 2 (fun z : NormalizedState × ℝ => normalizedMaxCurve z.1 t₀ z.2)
        (ball x₀ r ×ˢ Ioo (t₀ - ε) (t₀ + ε)) := by
  obtain ⟨r₀, hr₀, ε₀, hε₀, J₀, _, _, hJ₀⟩ := exists_normalizedMaxCurve_local_derivative x₀ t₀
  obtain ⟨r₁, hr₁, ε₁, hε₁, J, hcJ, hJ⟩ := exists_normalized_variation_family_contDiff_one x₀ t₀
  let r := min r₀ r₁
  let ε := min ε₀ ε₁
  let U := ball x₀ r ×ˢ Ioo (t₀ - ε) (t₀ + ε)
  have hr : 0 < r := lt_min hr₀ hr₁
  have hε : 0 < ε := lt_min hε₀ hε₁
  have hx₀ {x : NormalizedState} (hx : x ∈ ball x₀ r) : x ∈ ball x₀ r₀ :=
    ball_subset_ball (min_le_left _ _) hx
  have hx₁ {x : NormalizedState} (hx : x ∈ ball x₀ r) : x ∈ ball x₀ r₁ :=
    ball_subset_ball (min_le_right _ _) hx
  have ht₀ {u : ℝ} (hu : u ∈ Ioo (t₀ - ε) (t₀ + ε)) : u ∈ Ioo (t₀ - ε₀) (t₀ + ε₀) := by
    have H : ε ≤ ε₀ := min_le_left _ _
    constructor <;> linarith [hu.1, hu.2]
  have ht₁ {u : ℝ} (hu : u ∈ Ioo (t₀ - ε) (t₀ + ε)) : u ∈ Ioo (t₀ - ε₁) (t₀ + ε₁) := by
    have H : ε ≤ ε₁ := min_le_right _ _
    constructor <;> linarith [hu.1, hu.2]
  have hdom {x : NormalizedState} (hx : x ∈ ball x₀ r) :
      Ioo (t₀ - ε) (t₀ + ε) ⊆ normalizedMaxDomain x t₀ := fun _ ht => (hJ x (hx₁ hx)).1 (ht₁ ht)
  have hident (z : NormalizedState × ℝ) (hz : z ∈ U) : normalizedFlowDifferential z.1 t₀ z.2 = J z := by
    have hstart : t₀ ∈ Ioo (t₀ - ε) (t₀ + ε) := by constructor <;> linarith
    have hseg : uIcc t₀ z.2 ⊆ Ioo (t₀ - ε) (t₀ + ε) :=
      (convex_Ioo _ _).ordConnected.uIcc_subset hstart hz.2
    have hA : ContinuousOn (fun u =>
        ContinuousLinearMap.compL ℝ NormalizedState NormalizedState NormalizedState
          (normalizedDifferential (normalizedMaxCurve z.1 t₀ u))) (uIcc t₀ z.2) :=
      (ContinuousLinearMap.compL ℝ NormalizedState NormalizedState NormalizedState).continuous.comp_continuousOn
        ((contDiff_normalizedDifferential 1).continuous.comp_continuousOn
          (HasDerivAt.continuousOn (fun u hu => hasDerivAt_normalizedMaxCurve (hdom hz.1 (hseg hu)))))
    have Heq := ode_linear_solution_unique hA
      (fun u hu => ((hJ₀ z.1 (hx₀ hz.1)).2.2 u (ht₀ (hseg hu))).2)
      (fun u hu => (hJ z.1 (hx₁ hz.1)).2.2 u (ht₁ (hseg hu)))
      (by rw [(hJ₀ z.1 (hx₀ hz.1)).2.1, (hJ z.1 (hx₁ hz.1)).2.1])
    exact (((hJ₀ z.1 (hx₀ hz.1)).2.2 z.2 (ht₀ hz.2)).1.fderiv).trans Heq
  have hcJU : ContDiffOn ℝ 1 J U := hcJ.mono (fun _ hz => ⟨hx₁ hz.1, ht₁ hz.2⟩)
  have hcF : ContDiffOn ℝ 1 (fun z : NormalizedState × ℝ => normalizedMaxCurve z.1 t₀ z.2) U :=
    (contDiffOn_normalizedMaxCurve t₀).mono (fun _ hz => hdom hz.1 hz.2)
  let V : NormalizedState × ℝ → ℝ →L[ℝ] NormalizedState := fun z =>
    (ContinuousLinearMap.id ℝ ℝ).smulRight (normalizedField (normalizedMaxCurve z.1 t₀ z.2))
  have hcV : ContDiffOn ℝ 1 V U :=
    (ContinuousLinearMap.smulRightL ℝ ℝ NormalizedState (ContinuousLinearMap.id ℝ ℝ)).contDiff.comp_contDiffOn
      ((contDiff_normalizedField 1).comp_contDiffOn hcF)
  let D : NormalizedState × ℝ → (NormalizedState × ℝ →L[ℝ] NormalizedState) := fun z =>
    (J z).comp (ContinuousLinearMap.fst ℝ NormalizedState ℝ) +
      (V z).comp (ContinuousLinearMap.snd ℝ NormalizedState ℝ)
  have hcD : ContDiffOn ℝ 1 D U :=
    (hcJU.clm_comp contDiffOn_const).add (hcV.clm_comp contDiffOn_const)
  have hD (z : NormalizedState × ℝ) (hz : z ∈ U) : HasFDerivAt
      (fun w : NormalizedState × ℝ => normalizedMaxCurve w.1 t₀ w.2) (D z) z := by
    have H := hasFDerivAt_normalizedMaxCurve (hdom hz.1 hz.2)
    rw [hident z hz] at H
    convert! H using 1
  refine ⟨r, hr, ε, hε, fun _ hx => hdom hx, ?_⟩
  rw [show (2 : WithTop ℕ∞) = 1 + 1 by rfl,
    contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn (isOpen_ball.prod isOpen_Ioo).uniqueDiffOn]
  exact ⟨by simp, D, hcD, fun z hz => (hD z hz).hasFDerivWithinAt⟩

end BianchiIX
