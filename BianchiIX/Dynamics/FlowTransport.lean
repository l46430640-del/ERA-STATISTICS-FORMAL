import BianchiIX.Dynamics.GlobalVariation

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

def normalizedConstraintDifferential (x : NormalizedState) : NormalizedState →L[ℝ] ℝ :=
  fderiv ℝ stateConstraint x

theorem hasFDerivAt_stateConstraint (x : NormalizedState) :
    HasFDerivAt stateConstraint (normalizedConstraintDifferential x) x :=
  ((contDiff_stateConstraint 1).differentiable (by norm_num) x).hasFDerivAt

theorem normalizedMaxCurve_constraint {x : NormalizedState} {t₀ t : ℝ}
    (ht : t ∈ normalizedMaxDomain x t₀) :
    stateConstraint (normalizedMaxCurve x t₀ t) = stateConstraint x := by
  simpa only [normalizedMaxCurve_initial] using
    normalized_constraint_constant (convex_normalizedMaxDomain x t₀)
      (fun _ hu => hasDerivAt_normalizedMaxCurve hu) (initial_mem_normalizedMaxDomain x t₀) ht

theorem normalizedConstraintDifferential_field (x : NormalizedState) :
    normalizedConstraintDifferential x (normalizedField x) = 0 := by
  have hα := hasDerivAt_normalizedMaxCurve (initial_mem_normalizedMaxDomain x 0)
  have H := (hasFDerivAt_stateConstraint (normalizedMaxCurve x 0 0)).comp_hasDerivAt 0 hα
  simpa only [normalizedMaxCurve_initial] using H.unique (hasDerivAt_stateConstraint hα)

theorem normalizedConstraintDifferential_radial (x : NormalizedState) :
    normalizedConstraintDifferential x x = 2 * stateConstraint x := by
  have heq (u : ℝ) : stateConstraint (u • x) = u ^ 2 * stateConstraint x := by
    simp only [stateConstraint, constraint, shearSq, curvature, Pi.smul_apply, smul_eq_mul]
    ring
  have H := (hasFDerivAt_stateConstraint ((1 : ℝ) • x)).comp_hasDerivAt 1
    ((hasDerivAt_id (1 : ℝ)).smul_const x)
  have hd := ((hasDerivAt_id (1 : ℝ)).pow 2).mul_const (stateConstraint x)
  have H' : HasDerivAt (fun u : ℝ => u ^ 2 * stateConstraint x)
      (normalizedConstraintDifferential x x) 1 := by
    simpa only [Function.comp_def, id_eq, one_smul, heq] using H
  simpa using H'.unique hd

theorem normalizedConstraintDifferential_normal {x : NormalizedState} (hx : stateConstraint x = 1) :
    normalizedConstraintDifferential x ((1 / 2 : ℝ) • x) = 1 := by
  rw [map_smul, normalizedConstraintDifferential_radial, hx]
  norm_num

theorem normalizedConstraintDifferential_flow {x : NormalizedState} {t₀ t : ℝ}
    (ht : t ∈ normalizedMaxDomain x t₀) :
    (normalizedConstraintDifferential (normalizedMaxCurve x t₀ t)).comp
      (normalizedFlowDifferential x t₀ t) = normalizedConstraintDifferential x := by
  have hd := (hasFDerivAt_stateConstraint (normalizedMaxCurve x t₀ t)).comp x
    (hasFDerivAt_normalizedMaxCurve_initial ht)
  have heq : stateConstraint =ᶠ[𝓝 x] (fun y => stateConstraint (normalizedMaxCurve y t₀ t)) := by
    have hc : ContinuousAt (fun y : NormalizedState => (y, t)) x := by fun_prop
    filter_upwards [hc.eventually ((isOpen_normalizedFlowDomain t₀).mem_nhds ht)] with y hy
    exact (normalizedMaxCurve_constraint hy).symm
  exact (hd.congr_of_eventuallyEq heq).unique (hasFDerivAt_stateConstraint x)

theorem normalizedMaxCurve_shift {x : NormalizedState} {t₀ t u : ℝ}
    (hu : t₀ + u ∈ normalizedMaxDomain x t₀) (ht : t + u ∈ normalizedMaxDomain x t₀) :
    normalizedMaxCurve (normalizedMaxCurve x t₀ (t₀ + u)) t₀ t = normalizedMaxCurve x t₀ (t + u) := by
  have hd : t + u ∈ normalizedMaxDomain (normalizedMaxCurve x t₀ (t₀ + u)) (t₀ + u) := by
    rwa [normalizedMaxDomain_rebase hu]
  have hd' : t ∈ normalizedMaxDomain (normalizedMaxCurve x t₀ (t₀ + u)) t₀ := by
    apply (mem_normalizedMaxDomain_retime (t₀ := t₀ + u)).mpr
    convert! hd using 1
    ring
  have H := normalizedMaxCurve_retime (t₀ := t₀ + u) hd'
  rw [show t + (t₀ + u) - t₀ = t + u by ring] at H
  exact H.trans (normalizedMaxCurve_rebase hu ht)

theorem normalizedFlowDifferential_field {x : NormalizedState} {t₀ t : ℝ}
    (ht : t ∈ normalizedMaxDomain x t₀) :
    normalizedFlowDifferential x t₀ t (normalizedField x) =
      normalizedField (normalizedMaxCurve x t₀ t) := by
  have hstart : HasDerivAt (fun u => normalizedMaxCurve x t₀ (t₀ + u)) (normalizedField x) 0 := by
    have hd := hasDerivAt_normalizedMaxCurve (x₀ := x) (t₀ := t₀) (t := t₀ + 0)
      (by simpa using initial_mem_normalizedMaxDomain x t₀)
    convert! hd.scomp 0 ((hasDerivAt_id (0 : ℝ)).const_add t₀) using 1
    simp [normalizedMaxCurve_initial]
  have hend : HasDerivAt (fun u => normalizedMaxCurve x t₀ (t + u))
      (normalizedField (normalizedMaxCurve x t₀ t)) 0 := by
    have hd := hasDerivAt_normalizedMaxCurve (x₀ := x) (t₀ := t₀) (t := t + 0) (by simpa using ht)
    convert! hd.scomp 0 ((hasDerivAt_id (0 : ℝ)).const_add t) using 1
    simp
  have hp : HasFDerivAt (fun y => normalizedMaxCurve y t₀ t) (normalizedFlowDifferential x t₀ t)
      (normalizedMaxCurve x t₀ (t₀ + 0)) := by
    simpa only [add_zero, normalizedMaxCurve_initial] using hasFDerivAt_normalizedMaxCurve_initial ht
  have hcomp := hp.comp_hasDerivAt 0
    (show HasDerivAt (fun u => normalizedMaxCurve x t₀ (t₀ + u)) (normalizedField x) 0 from hstart)
  have heq : (fun u => normalizedMaxCurve x t₀ (t + u)) =ᶠ[𝓝 0]
      (fun u => normalizedMaxCurve (normalizedMaxCurve x t₀ (t₀ + u)) t₀ t) := by
    have hc (s : ℝ) : ContinuousAt (fun u : ℝ => s + u) 0 := by fun_prop
    have hs := (hc t₀).eventually ((isOpen_normalizedMaxDomain x t₀).mem_nhds
      (by simpa using initial_mem_normalizedMaxDomain x t₀))
    have he := (hc t).eventually ((isOpen_normalizedMaxDomain x t₀).mem_nhds (by simpa using ht))
    filter_upwards [hs, he] with u hu htu
    exact (normalizedMaxCurve_shift hu htu).symm
  exact (hcomp.congr_of_eventuallyEq heq).unique hend

end BianchiIX
