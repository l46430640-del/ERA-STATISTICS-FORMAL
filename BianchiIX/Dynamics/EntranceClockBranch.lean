import BianchiIX.Analysis.ImplicitEvent
import BianchiIX.Dynamics.EntranceFlowVariation
import BianchiIX.Dynamics.ProjectiveFlowSecondRegularity

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

def entranceRelativeClockDifferential (y : ProjectiveState) (t₀ t : ℝ) : ProjectiveState →L[ℝ] ℝ :=
  (fderiv ℝ entranceLogClock (projectiveOriginalFlow y t₀ t)).comp (projectiveFlowDifferential y t₀ t) -
    fderiv ℝ entranceLogClock y

def entranceClockTimeDifferential (y : ProjectiveState) (t₀ t : ℝ) : ProjectiveState →L[ℝ] ℝ :=
  -(entranceOriginalClockRate (projectiveOriginalFlow y t₀ t))⁻¹ • entranceRelativeClockDifferential y t₀ t

def entranceClockFlowDifferential (y : ProjectiveState) (t₀ t : ℝ) : ProjectiveState →L[ℝ] ProjectiveState :=
  projectiveFlowDifferential y t₀ t -
    (entranceRelativeClockDifferential y t₀ t).smulRight (entranceLogField (projectiveOriginalFlow y t₀ t))

theorem entranceClockFlowDifferential_apply {y : ProjectiveState} {t₀ t : ℝ}
    (hy : y 2 ≠ 0) (hv : projectiveOriginalFlow y t₀ t 2 ≠ 0) (w : ProjectiveState) :
    entranceClockFlowDifferential y t₀ t w = entranceProjectedFlowVariation y t₀ t w := by
  simp only [entranceClockFlowDifferential, entranceRelativeClockDifferential,
    sub_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.comp_apply, entranceLogClock_fderiv hy, entranceLogClock_fderiv hv]
  rfl

/-- The fixed relative clock is realized by nearby exact trajectories, not just a tangent projection. -/
theorem exists_entranceClock_branch {y : ProjectiveState} {t₀ t : ℝ}
    (hD : 0 < projectiveStateDenom y) (ht : t ∈ normalizedMaxDomain (fromProjectiveState y) t₀)
    (hA : 0 < 1 + normalizedMaxCurve (fromProjectiveState y) t₀ t 0)
    (hy : y 2 ≠ 0) (hv : projectiveOriginalFlow y t₀ t 2 ≠ 0)
    (hclock : entranceClockRate (projectiveOriginalFlow y t₀ t) ≠ 0) :
    ∃ τ : ProjectiveState → ℝ, τ y = t ∧ ContDiffAt ℝ 2 τ y ∧
      HasFDerivAt τ (entranceClockTimeDifferential y t₀ t) y ∧
      (∀ᶠ z in 𝓝 y, τ z ∈ normalizedMaxDomain (fromProjectiveState z) t₀ ∧
        0 < 1 + normalizedMaxCurve (fromProjectiveState z) t₀ (τ z) 0 ∧
        entranceLogClock (projectiveOriginalFlow z t₀ (τ z)) - entranceLogClock z =
          entranceLogClock (projectiveOriginalFlow y t₀ t) - entranceLogClock y) ∧
      (∀ᶠ z : ProjectiveState × ℝ in 𝓝 (y, t),
        (entranceLogClock (projectiveOriginalFlow z.1 t₀ z.2) - entranceLogClock z.1 =
          entranceLogClock (projectiveOriginalFlow y t₀ t) - entranceLogClock y ↔ τ z.1 = z.2)) ∧
      ContDiffAt ℝ 2 (fun z => projectiveOriginalFlow z t₀ (τ z)) y ∧
      HasFDerivAt (fun z => projectiveOriginalFlow z t₀ (τ z)) (entranceClockFlowDifferential y t₀ t) y := by
  let Q : ProjectiveState × ℝ → ℝ := fun z =>
    entranceLogClock (projectiveOriginalFlow z.1 t₀ z.2) - entranceLogClock z.1
  have hF := contDiffAt_projectiveOriginalFlow_two hD ht hA
  have hQ : ContDiffAt ℝ 2 Q (y, t) :=
    ((contDiffAt_entranceLogClock 2 hv).comp (y, t) hF).sub
      ((contDiffAt_entranceLogClock 2 hy).comp (y, t) contDiffAt_fst)
  have hc : stateConstraint (normalizedMaxCurve (fromProjectiveState y) t₀ t) = 1 :=
    (normalizedMaxCurve_constraint ht).trans (fromProjectiveState_constraint (ne_of_gt hD))
  have hr : entranceOriginalClockRate (projectiveOriginalFlow y t₀ t) ≠ 0 :=
    mul_ne_zero (div_ne_zero (by norm_num) (ne_of_gt (toProjectiveState_denom_pos hA hc))) hclock
  have htime : HasDerivAt (fun u => Q (y, u))
      (entranceOriginalClockRate (projectiveOriginalFlow y t₀ t)) t := by
    have H := ((contDiffAt_entranceLogClock 2 hv).differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt t
      (hasDerivAt_projectiveOriginalFlow_time hD ht hA)
    rw [entranceLogClock_fderiv_field hv] at H
    simpa only [Function.comp_def] using H.sub_const (entranceLogClock y)
  have hleft : (fderiv ℝ Q (y, t)).comp (ContinuousLinearMap.inl ℝ ProjectiveState ℝ) =
      entranceRelativeClockDifferential y t₀ t := by
    have H := ((hQ.differentiableAt (by norm_num)).hasFDerivAt.comp y
      (hasFDerivAt_prodMk_left (𝕜 := ℝ) y t))
    have H' := (((contDiffAt_entranceLogClock 2 hv).differentiableAt (by norm_num)).hasFDerivAt.comp y
      (hasFDerivAt_projectiveOriginalFlow_initial hD ht hA)).sub
      ((contDiffAt_entranceLogClock 2 hy).differentiableAt (by norm_num)).hasFDerivAt
    exact H.unique H'
  obtain ⟨τ, hτ, hcτ, hdτ, hhit, huniq⟩ := exists_scalar_event_branch_two hQ htime hr
  rw [hleft] at hdτ
  have hgraph : Tendsto (fun z => (z, τ z)) (𝓝 y) (𝓝 (y, t)) := by
    simpa only [hτ, id_eq] using (continuousAt_id.prodMk hcτ.continuousAt).tendsto
  have hparam : ContDiffAt ℝ 2 (fun z : ProjectiveState × ℝ => (fromProjectiveState z.1, z.2)) (y, t) :=
    ((contDiffAt_fromProjectiveState 2 (ne_of_gt hD)).comp (y, t) contDiffAt_fst).prodMk contDiffAt_snd
  have hdomain : ∀ᶠ z : ProjectiveState × ℝ in 𝓝 (y, t),
      z.2 ∈ normalizedMaxDomain (fromProjectiveState z.1) t₀ :=
    hparam.continuousAt.tendsto.eventually ((isOpen_normalizedFlowDomain t₀).mem_nhds ht)
  have hN : ContinuousAt (fun z : ProjectiveState × ℝ =>
      normalizedMaxCurve (fromProjectiveState z.1) t₀ z.2) (y, t) := by
    simpa only [Function.comp_def] using
      ((contDiffAt_normalizedMaxCurve_two ht).comp (y, t) hparam).continuousAt
  have hscale : ContinuousAt (fun z : ProjectiveState × ℝ =>
      1 + normalizedMaxCurve (fromProjectiveState z.1) t₀ z.2 0) (y, t) :=
    continuousAt_const.add ((continuous_apply 0).continuousAt.comp hN)
  have hchart : ∀ᶠ z : ProjectiveState × ℝ in 𝓝 (y, t),
      0 < 1 + normalizedMaxCurve (fromProjectiveState z.1) t₀ z.2 0 :=
    hscale.eventually (isOpen_Ioi.mem_nhds hA)
  have hFc : ContDiffAt ℝ 2 (fun z : ProjectiveState × ℝ => projectiveOriginalFlow z.1 t₀ z.2) (y, τ y) := by
    simpa only [hτ] using hF
  have hFd : HasFDerivAt (fun z : ProjectiveState × ℝ => projectiveOriginalFlow z.1 t₀ z.2)
      ((projectiveFlowDifferential y t₀ t).coprod
        ((ContinuousLinearMap.id ℝ ℝ).smulRight (projectiveOriginalField (projectiveOriginalFlow y t₀ t))))
      (y, τ y) := by
    simpa only [hτ] using hasFDerivAt_projectiveOriginalFlow hD ht hA
  refine ⟨τ, hτ, hcτ, hdτ, ?_, huniq, ?_, ?_⟩
  · filter_upwards [hgraph.eventually hdomain, hgraph.eventually hchart, hhit] with z hz ha heq
    exact ⟨hz, ha, heq⟩
  · simpa only [Function.comp_def, id_eq] using hFc.comp y (contDiffAt_id.prodMk hcτ)
  · have H := hFd.comp y ((hasFDerivAt_id y).prodMk hdτ)
    convert! H using 1
    ext w i
    simp only [entranceClockFlowDifferential, sub_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coprod_apply, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.id_apply, smul_apply,
      projectiveOriginalField_entranceLog hclock, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul]
    field_simp
    ring

end BianchiIX
