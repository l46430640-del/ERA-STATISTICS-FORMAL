import BianchiIX.Dynamics.SectionFlux
import BianchiIX.Dynamics.Events

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

theorem hasFDerivAt_normalized_arrival {x : NormalizedState} {t₀ : ℝ}
    {τ : NormalizedState → ℝ} (ht : τ x ∈ normalizedMaxDomain x t₀)
    (hτ : DifferentiableAt ℝ τ x) :
    HasFDerivAt (fun y => normalizedMaxCurve y t₀ (τ y))
      (normalizedFlowDifferential x t₀ (τ x) +
        (fderiv ℝ τ x).smulRight (normalizedField (normalizedMaxCurve x t₀ (τ x)))) x := by
  convert! (hasFDerivAt_normalizedMaxCurve ht).comp x
    ((hasFDerivAt_id x).prodMk hτ.hasFDerivAt) using 1

theorem normalizedConstraintDifferential_arrival {x : NormalizedState} {t₀ : ℝ}
    {τ : NormalizedState → ℝ} (ht : τ x ∈ normalizedMaxDomain x t₀)
    (hτ : DifferentiableAt ℝ τ x) :
    (normalizedConstraintDifferential (normalizedMaxCurve x t₀ (τ x))).comp
      (fderiv ℝ (fun y => normalizedMaxCurve y t₀ (τ y)) x) = normalizedConstraintDifferential x := by
  rw [(hasFDerivAt_normalized_arrival ht hτ).fderiv]
  ext v
  simp only [ContinuousLinearMap.comp_apply, add_apply,
    ContinuousLinearMap.smulRight_apply, map_add, map_smul,
    normalizedConstraintDifferential_field, smul_zero, add_zero]
  exact congrArg (fun L : NormalizedState →L[ℝ] ℝ => L v) (normalizedConstraintDifferential_flow ht)

/-- The actual derivative of a moving-time map has the same flux multiplier as the fixed-time flow. -/
theorem normalizedSectionFlux_arrival {x : NormalizedState} {t₀ : ℝ}
    {τ : NormalizedState → ℝ} (hpos : positiveWalls x) (hcon : stateConstraint x = 1)
    (ht : τ x ∈ normalizedMaxDomain x t₀) (hτ : DifferentiableAt ℝ τ x)
    (v : Fin 3 → NormalizedState) (hv : ∀ i, normalizedConstraintDifferential x (v i) = 0) :
    normalizedSectionFlux (normalizedMaxCurve x t₀ (τ x))
        (fun i => fderiv ℝ (fun y => normalizedMaxCurve y t₀ (τ y)) x (v i)) =
      normalizedVolumeJacobian x t₀ (τ x) * normalizedSectionFlux x v := by
  rw [(hasFDerivAt_normalized_arrival ht hτ).fderiv,
    ← normalizedSectionFlux_flow hpos hcon ht v hv]
  unfold normalizedSectionFlux normalizedConstraintVolume
  congr 1
  exact normalizedSectionFlux_add_flow (normalizedMaxCurve x t₀ (τ x))
    ((1 / 2 : ℝ) • normalizedMaxCurve x t₀ (τ x))
    (fun i => normalizedFlowDifferential x t₀ (τ x) (v i))
    (fun i => fderiv ℝ τ x (v i))

theorem normalizedSectionFlux_arrival_abs {x : NormalizedState} {t₀ : ℝ}
    {τ : NormalizedState → ℝ} (hpos : positiveWalls x) (hcon : stateConstraint x = 1)
    (ht : τ x ∈ normalizedMaxDomain x t₀) (hτ : DifferentiableAt ℝ τ x)
    (v : Fin 3 → NormalizedState) (hv : ∀ i, normalizedConstraintDifferential x (v i) = 0) :
    |normalizedSectionFlux (normalizedMaxCurve x t₀ (τ x))
        (fun i => fderiv ℝ (fun y => normalizedMaxCurve y t₀ (τ y)) x (v i))| =
      Real.exp (∫ u in t₀..τ x, normalizedCorrectedDivergence (normalizedMaxCurve x t₀ u)) *
        |normalizedSectionFlux x v| := by
  rw [normalizedSectionFlux_arrival hpos hcon ht hτ v hv,
    normalizedVolumeJacobian_eq_exp_integral hpos hcon ht, abs_mul, abs_of_pos (Real.exp_pos _)]

theorem normalizedSectionFlux_arrival_strict {x : NormalizedState} {t₀ : ℝ}
    {τ : NormalizedState → ℝ} (hpos : positiveWalls x) (hcon : stateConstraint x = 1)
    (htt : t₀ < τ x) (hτ : DifferentiableAt ℝ τ x)
    (v : Fin 3 → NormalizedState) (hv : ∀ i, normalizedConstraintDifferential x (v i) = 0)
    (hnonzero : normalizedSectionFlux x v ≠ 0) :
    |normalizedSectionFlux x v| <
      |normalizedSectionFlux (normalizedMaxCurve x t₀ (τ x))
        (fun i => fderiv ℝ (fun y => normalizedMaxCurve y t₀ (τ y)) x (v i))| := by
  have ht := normalizedMaxDomain_contains_Ici hpos hcon t₀ htt.le
  have hJ := normalizedVolumeJacobian_gt_one hpos hcon htt
  rw [normalizedSectionFlux_arrival hpos hcon ht hτ v hv, abs_mul,
    abs_of_pos (lt_trans zero_lt_one hJ)]
  simpa only [one_mul] using mul_lt_mul_of_pos_right hJ (abs_pos.mpr hnonzero)

/-- The local implicit event constructed from the exact flow satisfies the flux formula. -/
theorem exists_normalized_event_with_flux {x : NormalizedState} {t₀ t : ℝ}
    {g : NormalizedState → ℝ} (hpos : positiveWalls x) (hcon : stateConstraint x = 1)
    (ht : t ∈ normalizedMaxDomain x t₀)
    (hg : ContDiffAt ℝ 1 g (normalizedMaxCurve x t₀ t))
    (htrans : normalizedEventRate g x t₀ t ≠ 0) :
    ∃ τ : NormalizedState → ℝ, τ x = t ∧ ContDiffAt ℝ 1 τ x ∧
      (∀ᶠ y in 𝓝 x, τ y ∈ normalizedMaxDomain y t₀ ∧
        g (normalizedMaxCurve y t₀ (τ y)) = g (normalizedMaxCurve x t₀ t)) ∧
      ContDiffAt ℝ 1 (fun y => normalizedMaxCurve y t₀ (τ y)) x ∧
      ∀ v : Fin 3 → NormalizedState, (∀ i, normalizedConstraintDifferential x (v i) = 0) →
        |normalizedSectionFlux (normalizedMaxCurve x t₀ t)
            (fun i => fderiv ℝ (fun y => normalizedMaxCurve y t₀ (τ y)) x (v i))| =
          Real.exp (∫ u in t₀..t, normalizedCorrectedDivergence (normalizedMaxCurve x t₀ u)) *
            |normalizedSectionFlux x v| := by
  obtain ⟨τ, hτ, hcτ, _, hhit, _, hcMap, _⟩ := exists_normalized_event ht hg htrans
  refine ⟨τ, hτ, hcτ, hhit, hcMap, fun v hv => ?_⟩
  have H := normalizedSectionFlux_arrival_abs hpos hcon
    (show τ x ∈ normalizedMaxDomain x t₀ by rwa [hτ])
    (hcτ.differentiableAt (by norm_num)) v hv
  simpa only [hτ] using H

end BianchiIX
