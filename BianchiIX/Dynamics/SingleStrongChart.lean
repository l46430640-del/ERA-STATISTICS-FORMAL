import BianchiIX.Dynamics.StableSingleStrongWall

noncomputable section

namespace BianchiIX

open Set Filter MeasureTheory
open scoped Topology

theorem normalized_single_strong_zeros {x : NormalizedState} {t₀ t : ℝ}
    (hx3 : x 3 = 0) (hx4 : x 4 = 0) (ht : t ∈ normalizedMaxDomain x t₀) :
    normalizedMaxCurve x t₀ t 3 = 0 ∧ normalizedMaxCurve x t₀ t 4 = 0 := by
  have H (i : Fin 3) := normalized_wall_sign (convex_normalizedMaxDomain x t₀) (isOpen_normalizedMaxDomain x t₀)
    (fun _ hs => hasDerivAt_normalizedMaxCurve hs) (initial_mem_normalizedMaxDomain x t₀) ht i
  simp only [normalizedMaxCurve_initial] at H
  exact ⟨(H 1).1.mpr hx3, (H 2).1.mpr hx4⟩

theorem normalized_single_strong_shear {x : NormalizedState} {t₀ t : ℝ}
    (hx3 : x 3 = 0) (hx4 : x 4 = 0) (ht : t ∈ normalizedMaxDomain x t₀) :
    normalizedMaxCurve x t₀ t 1 = x 1 * Real.exp (∫ s in t₀..t, normalizedMaxCurve x t₀ s 2 ^ 2) := by
  have hc : ContinuousOn (fun s => normalizedMaxCurve x t₀ s 2 ^ 2) (normalizedMaxDomain x t₀) :=
    ((continuous_apply 2).comp_continuousOn
      (HasDerivAt.continuousOn (fun s hs => hasDerivAt_normalizedMaxCurve (x₀ := x) (t₀ := t₀) hs))).pow 2
  have hd (s : ℝ) (hs : s ∈ normalizedMaxDomain x t₀) :
      HasDerivAt (fun r => normalizedMaxCurve x t₀ r 1)
        (normalizedMaxCurve x t₀ s 2 ^ 2 * normalizedMaxCurve x t₀ s 1) s := by
    obtain ⟨h3, h4⟩ := normalized_single_strong_zeros hx3 hx4 hs
    simpa [normalizedField, shearMinus, curvature, h3, h4] using
      hasDerivAt_pi.mp (hasDerivAt_normalizedMaxCurve hs) 1
  simpa only [normalizedMaxCurve_initial] using homogeneous_solution_eq_exp_integral
    (convex_normalizedMaxDomain x t₀) (isOpen_normalizedMaxDomain x t₀) hc hd
    (initial_mem_normalizedMaxDomain x t₀) ht

theorem normalized_single_strong_region {x : NormalizedState} {t₀ t : ℝ}
    (hx : stateConstraint x = 1) (hx1 : 0 < x 1) (hx2 : 0 < x 2)
    (hx3 : x 3 = 0) (hx4 : x 4 = 0) (ht : t ∈ normalizedMaxDomain x t₀) :
    0 < normalizedMaxCurve x t₀ t 1 ∧ 0 < normalizedMaxCurve x t₀ t 2 ∧
      normalizedMaxCurve x t₀ t 3 = 0 ∧ normalizedMaxCurve x t₀ t 4 = 0 ∧
      0 < 1 + normalizedMaxCurve x t₀ t 0 := by
  have hs : 0 < normalizedMaxCurve x t₀ t 1 := by
    rw [normalized_single_strong_shear hx3 hx4 ht]
    exact mul_pos hx1 (Real.exp_pos _)
  have hu : 0 < normalizedMaxCurve x t₀ t 2 := by
    have H := normalized_wall_pos (convex_normalizedMaxDomain x t₀) (isOpen_normalizedMaxDomain x t₀)
      (fun _ hr => hasDerivAt_normalizedMaxCurve hr) (initial_mem_normalizedMaxDomain x t₀) ht 0
    simp only [normalizedMaxCurve_initial] at H
    exact H hx2
  obtain ⟨h3, h4⟩ := normalized_single_strong_zeros hx3 hx4 ht
  have hcon := (normalizedMaxCurve_constraint ht).trans hx
  have hsq : normalizedMaxCurve x t₀ t 0 ^ 2 + normalizedMaxCurve x t₀ t 1 ^ 2 +
      normalizedMaxCurve x t₀ t 2 ^ 2 = 1 := by
    simpa [stateConstraint, constraint, shearSq, curvature, h3, h4] using hcon
  refine ⟨hs, hu, h3, h4, ?_⟩
  nlinarith only [hsq, sq_pos_of_pos hs, sq_nonneg (normalizedMaxCurve x t₀ t 2),
    sq_nonneg (normalizedMaxCurve x t₀ t 0 + 1)]

theorem singleStrongFlow_global_region {m u t : ℝ} (hm : 0 < m) (hu : 0 < u) (ht : 0 ≤ t) :
    0 < stableOriginalFlow ![m, u, 0] t 0 ∧ 0 < stableOriginalFlow ![m, u, 0] t 1 ∧
      stableOriginalFlow ![m, u, 0] t 2 = 0 ∧
      0 < normalizedProjectiveRate (fromProjectiveState (stableInclusion ![m, u, 0])) 0 t := by
  let x := fromProjectiveState (stableInclusion ![m, u, 0])
  have hD : 0 < projectiveStateDenom (stableInclusion ![m, u, 0]) := by
    rw [stableBoundaryDenom_eq]
    exact stableBoundaryDenom_pos _
  have hx : stateConstraint x = 1 := fromProjectiveState_constraint hD.ne'
  have hroot : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have h1 : 0 < x 1 := by
    change 0 < (6 / projectiveStateDenom (stableInclusion ![m, u, 0])) * m / Real.sqrt 3
    positivity
  have h2 : 0 < x 2 := by
    change 0 < (6 / projectiveStateDenom (stableInclusion ![m, u, 0])) * u / Real.sqrt 3
    positivity
  have h3 : x 3 = 0 := by simp [x, fromProjectiveState, stableInclusion_apply]
  have h4 : x 4 = 0 := by simp [x, fromProjectiveState, stableInclusion_apply]
  have hdom := normalizedMaxDomain_contains_Ici_of_constraint hx 0 ht
  obtain ⟨hs, ha, _, hc, hA⟩ := normalized_single_strong_region hx h1 h2 h3 h4 hdom
  refine ⟨?_, ?_, ?_, hA⟩
  · change 0 < Real.sqrt 3 * normalizedMaxCurve x 0 t 1 / (1 + normalizedMaxCurve x 0 t 0)
    positivity
  · change 0 < Real.sqrt 3 * normalizedMaxCurve x 0 t 2 / (1 + normalizedMaxCurve x 0 t 0)
    positivity
  · change Real.sqrt 3 * normalizedMaxCurve x 0 t 4 / (1 + normalizedMaxCurve x 0 t 0) = 0
    rw [hc, mul_zero, zero_div]

theorem hasDerivAt_singleStrongFlow {m u t : ℝ} (hm : 0 < m) (hu : 0 < u) (ht : 0 ≤ t) :
    HasDerivAt (stableOriginalFlow ![m, u, 0])
      (stableOriginalField (stableOriginalFlow ![m, u, 0] t)) t := by
  have hD : 0 < projectiveStateDenom (stableInclusion ![m, u, 0]) := by
    rw [stableBoundaryDenom_eq]
    exact stableBoundaryDenom_pos _
  have hx := fromProjectiveState_constraint hD.ne'
  have hdom := normalizedMaxDomain_contains_Ici_of_constraint hx 0 ht
  have hA := (singleStrongFlow_global_region hm hu ht).2.2.2
  have H := stableRestriction.hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_projectiveOriginalFlow_time hD hdom hA)
  rw [stableOriginalField_restriction (stableProjectiveFlow_active_zero _ ht)] at H
  exact H

end BianchiIX
