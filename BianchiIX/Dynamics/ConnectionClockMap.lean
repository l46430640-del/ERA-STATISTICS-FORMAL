import BianchiIX.Dynamics.ConnectionFlowVariation
import BianchiIX.Dynamics.ProjectiveFlowSecondRegularity
import Mathlib.Analysis.Calculus.ImplicitContDiff

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

/-- The local map at fixed relative logarithmic clock has the projected actual derivative. -/
theorem exists_connection_relative_clock_map {y : ProjectiveState} {t₀ t : ℝ}
    (hD : 0 < projectiveStateDenom y) (ht : t ∈ normalizedMaxDomain (fromProjectiveState y) t₀)
    (hA : 0 < 1 + normalizedMaxCurve (fromProjectiveState y) t₀ t 0)
    (hw₀ : y 3 ≠ 0) (hw : projectiveOriginalFlow y t₀ t 3 ≠ 0)
    (hclock : connectionClockRate (projectiveOriginalFlow y t₀ t) ≠ 0) :
    ∃ τ : ProjectiveState → ℝ, τ y = t ∧ ContDiffAt ℝ 2 τ y ∧
      (∀ᶠ z in 𝓝 y, τ z ∈ normalizedMaxDomain (fromProjectiveState z) t₀ ∧
        connectionLogClock (projectiveOriginalFlow z t₀ (τ z)) - connectionLogClock z =
          connectionLogClock (projectiveOriginalFlow y t₀ t) - connectionLogClock y) ∧
      (∀ᶠ z : ProjectiveState × ℝ in 𝓝 (y, t),
        connectionLogClock (projectiveOriginalFlow z.1 t₀ z.2) - connectionLogClock z.1 =
          connectionLogClock (projectiveOriginalFlow y t₀ t) - connectionLogClock y ↔ τ z.1 = z.2) ∧
      ContDiffAt ℝ 2 (fun z => projectiveOriginalFlow z t₀ (τ z)) y ∧
      (∀ v : ProjectiveState, fderiv ℝ (fun z => projectiveOriginalFlow z t₀ (τ z)) y v =
        connectionProjectedFlowVariation y t₀ t v) := by
  let Q : ProjectiveState × ℝ → ℝ := fun z =>
    connectionLogClock (projectiveOriginalFlow z.1 t₀ z.2) - connectionLogClock z.1
  have hcFlow := contDiffAt_projectiveOriginalFlow_two hD ht hA
  have hcQ : ContDiffAt ℝ 2 Q (y, t) :=
    ((contDiffAt_connectionLogClock 2 hw).comp (y, t) hcFlow).sub
      ((contDiffAt_connectionLogClock 2 hw₀).comp (y, t) contDiffAt_fst)
  have hc : stateConstraint (normalizedMaxCurve (fromProjectiveState y) t₀ t) = 1 :=
    (normalizedMaxCurve_constraint ht).trans (fromProjectiveState_constraint (ne_of_gt hD))
  have hr : connectionOriginalClockRate (projectiveOriginalFlow y t₀ t) ≠ 0 :=
    mul_ne_zero (div_ne_zero (by norm_num) (ne_of_gt (toProjectiveState_denom_pos hA hc))) hclock
  have hdQ : HasDerivAt (fun s => Q (y, s)) (connectionOriginalClockRate (projectiveOriginalFlow y t₀ t)) t := by
    have H := (((contDiffAt_connectionLogClock 1 hw).differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt t
      (hasDerivAt_projectiveOriginalFlow_time hD ht hA)).sub_const (connectionLogClock y)
    simpa only [Q, Function.comp_def, connectionLogClock_fderiv_field hw] using H
  have htime : (fderiv ℝ Q (y, t)).comp (ContinuousLinearMap.inr ℝ ProjectiveState ℝ) =
      connectionOriginalClockRate (projectiveOriginalFlow y t₀ t) • ContinuousLinearMap.id ℝ ℝ := by
    have H := ((hcQ.differentiableAt (by norm_num)).hasFDerivAt.comp t
      (hasFDerivAt_prodMk_right y t)).unique hdQ.hasFDerivAt
    rw [H]
    ext
    simp [mul_comm]
  have hinv : ((fderiv ℝ Q (y, t)).comp (ContinuousLinearMap.inr ℝ ProjectiveState ℝ)).IsInvertible := by
    rw [htime]
    apply ContinuousLinearMap.IsInvertible.of_inverse
      (g := (connectionOriginalClockRate (projectiveOriginalFlow y t₀ t))⁻¹ • ContinuousLinearMap.id ℝ ℝ)
    · ext
      simp [hr]
    · ext
      simp [hr]
  let τ := hcQ.implicitFunction (by norm_num) hinv
  have hτ : τ y = t := hcQ.implicitFunction_apply_self (by norm_num) hinv
  have hcτ : ContDiffAt ℝ 2 τ y := hcQ.contDiffAt_implicitFunction (by norm_num) hinv
  have hhit : ∀ᶠ z in 𝓝 y, Q (z, τ z) = Q (y, t) := hcQ.eventually_apply_implicitFunction (by norm_num) hinv
  have hdom : ∀ᶠ z in 𝓝 y, τ z ∈ normalizedMaxDomain (fromProjectiveState z) t₀ := by
    have hmap := (contDiffAt_fromProjectiveState 2 (ne_of_gt hD)).continuousAt.prodMk hcτ.continuousAt
    have hbase : (fromProjectiveState y, τ y) ∈ normalizedFlowDomain t₀ := by
      change τ y ∈ normalizedMaxDomain (fromProjectiveState y) t₀
      rwa [hτ]
    exact hmap.eventually ((isOpen_normalizedFlowDomain t₀).mem_nhds hbase)
  have hFlowτ : ContDiffAt ℝ 2 (fun z : ProjectiveState × ℝ => projectiveOriginalFlow z.1 t₀ z.2) (y, τ y) := by
    simpa only [hτ] using hcFlow
  have hcP : ContDiffAt ℝ 2 (fun z => projectiveOriginalFlow z t₀ (τ z)) y := by
    simpa only [Function.comp_def, id_eq] using hFlowτ.comp y (contDiffAt_id.prodMk hcτ)
  refine ⟨τ, hτ, hcτ, hdom.and hhit, hcQ.eventually_apply_eq_iff_implicitFunction (by norm_num) hinv, hcP, ?_⟩
  intro v
  have hdFlow : HasFDerivAt (fun z : ProjectiveState × ℝ => projectiveOriginalFlow z.1 t₀ z.2)
      ((projectiveFlowDifferential y t₀ t).coprod
        ((ContinuousLinearMap.id ℝ ℝ).smulRight (projectiveOriginalField (projectiveOriginalFlow y t₀ t)))) (y, τ y) := by
    simpa only [hτ] using hasFDerivAt_projectiveOriginalFlow hD ht hA
  have hdP : HasFDerivAt (fun z => projectiveOriginalFlow z t₀ (τ z))
      (((projectiveFlowDifferential y t₀ t).coprod
        ((ContinuousLinearMap.id ℝ ℝ).smulRight (projectiveOriginalField (projectiveOriginalFlow y t₀ t)))).comp
          ((ContinuousLinearMap.id ℝ ProjectiveState).prod (fderiv ℝ τ y))) y := by
    simpa only [Function.comp_def, id_eq] using hdFlow.comp y
      ((hasFDerivAt_id y).prodMk ((hcτ.differentiableAt (by norm_num)).hasFDerivAt))
  have hP : fderiv ℝ (fun z => projectiveOriginalFlow z t₀ (τ z)) y v =
      projectiveFlowDifferential y t₀ t v + fderiv ℝ τ y v • projectiveOriginalField (projectiveOriginalFlow y t₀ t) := by
    rw [hdP.fderiv]
    rfl
  have hlog : HasFDerivAt connectionLogClock (fderiv ℝ connectionLogClock (projectiveOriginalFlow y t₀ t))
      (projectiveOriginalFlow y t₀ (τ y)) := by
    simpa only [hτ] using ((contDiffAt_connectionLogClock 1 hw).differentiableAt (by norm_num)).hasFDerivAt
  have hconst : HasFDerivAt (fun z => Q (z, τ z)) 0 y :=
    (hasFDerivAt_const (𝕜 := ℝ) (Q (y, t)) y).congr_of_eventuallyEq hhit
  have hcomp := HasFDerivAt.comp (g := connectionLogClock)
    (f := fun z : ProjectiveState => projectiveOriginalFlow z t₀ (τ z)) y hlog hdP
  have heq := (hcomp.sub
    ((contDiffAt_connectionLogClock 1 hw₀).differentiableAt (by norm_num)).hasFDerivAt).unique hconst
  have H := congrArg (fun L : ProjectiveState →L[ℝ] ℝ => L v) heq
  change fderiv ℝ connectionLogClock (projectiveOriginalFlow y t₀ t)
      (projectiveFlowDifferential y t₀ t v + fderiv ℝ τ y v • projectiveOriginalField (projectiveOriginalFlow y t₀ t)) -
      fderiv ℝ connectionLogClock y v = 0 at H
  rw [map_add, map_smul, connectionLogClock_fderiv hw, connectionLogClock_fderiv_field hw,
    connectionLogClock_fderiv hw₀] at H
  have hscalar : fderiv ℝ τ y v * connectionOriginalClockRate (projectiveOriginalFlow y t₀ t) =
      -(projectiveFlowDifferential y t₀ t v 3 / projectiveOriginalFlow y t₀ t 3 - v 3 / y 3) := by
    change _ + fderiv ℝ τ y v * connectionOriginalClockRate (projectiveOriginalFlow y t₀ t) - _ = 0 at H
    linarith only [H]
  rw [hP, projectiveOriginalField_connectionLog hclock, smul_smul, hscalar]
  simp only [connectionProjectedFlowVariation, connectionClockProjection, neg_smul, sub_eq_add_neg]

end BianchiIX
