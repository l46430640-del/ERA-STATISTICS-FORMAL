import BianchiIX.Dynamics.CoreFlowVariation
import BianchiIX.Dynamics.Events

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

def normalizedCoreAngle (x : NormalizedState) : ℝ := projectiveCoreAngle (toProjectiveState x)

def coreClockProjectionLinear (y : ProjectiveState) : ProjectiveState →L[ℝ] CoreAngleState :=
  fderiv ℝ toCoreAngleState y - (fderiv ℝ projectiveCoreAngle y).smulRight
    (coreAngleField (projectiveCoreAngle y) (toCoreAngleState y))

def coreAngleArrivalDifferential (y : ProjectiveState) (t₀ t : ℝ) :
    ProjectiveState →L[ℝ] CoreAngleState :=
  (coreClockProjectionLinear (projectiveOriginalFlow y t₀ t)).comp (projectiveFlowDifferential y t₀ t)

theorem coreAngleArrivalDifferential_apply (y : ProjectiveState) (t₀ t : ℝ) (w : ProjectiveState) :
    coreAngleArrivalDifferential y t₀ t w = coreProjectedFlowVariation y t₀ t w := rfl

theorem contDiffAt_normalizedCoreAngle (n : WithTop ℕ∞) {x : NormalizedState}
    (hA : 1 + x 0 ≠ 0) (hV : 0 < toProjectiveState x 2) :
    ContDiffAt ℝ n normalizedCoreAngle x :=
  (contDiffAt_projectiveCoreAngle n hV).comp x (contDiffAt_toProjectiveState n hA)

theorem normalizedCoreAngle_fderiv {x : NormalizedState}
    (hA : 1 + x 0 ≠ 0) (hV : 0 < toProjectiveState x 2) (v : NormalizedState) :
    fderiv ℝ normalizedCoreAngle x v =
      fderiv ℝ projectiveCoreAngle (toProjectiveState x) (fderiv ℝ toProjectiveState x v) := by
  have hd := ((contDiffAt_projectiveCoreAngle 1 hV).differentiableAt (by norm_num)).hasFDerivAt.comp x
    ((contDiffAt_toProjectiveState 1 hA).differentiableAt (by norm_num)).hasFDerivAt
  rw [show fderiv ℝ normalizedCoreAngle x = _ from hd.fderiv]
  rfl

theorem normalizedCoreAngle_fderiv_field {x : NormalizedState}
    (hA : 1 + x 0 ≠ 0) (hc : stateConstraint x = 1) (hV : 0 < toProjectiveState x 2) :
    fderiv ℝ normalizedCoreAngle x (normalizedField x) = coreOriginalClockRate (toProjectiveState x) := by
  rw [normalizedCoreAngle_fderiv hA hV, toProjectiveState_fderiv_field hA hc,
    ← projective_inverse_scale hA hc]
  exact projectiveCoreAngle_fderiv_field hV

/-- The derivative of a genuine fixed-angle event is exactly the clock projection. -/
theorem coreAngle_event_projection {x : NormalizedState} {t₀ t : ℝ}
    (hA : 1 + normalizedMaxCurve x t₀ t 0 ≠ 0)
    (hc : stateConstraint (normalizedMaxCurve x t₀ t) = 1)
    (hV : 0 < toProjectiveState (normalizedMaxCurve x t₀ t) 2)
    (hrate : coreOriginalClockRate (toProjectiveState (normalizedMaxCurve x t₀ t)) ≠ 0)
    (v : NormalizedState) :
    let X := normalizedMaxCurve x t₀ t
    let y := toProjectiveState X
    fderiv ℝ toCoreAngleState y
      (fderiv ℝ toProjectiveState X (normalizedEventDifferential normalizedCoreAngle x t₀ t v)) =
      coreClockProjection y (fderiv ℝ toProjectiveState X (normalizedFlowDifferential x t₀ t v)) := by
  intro X y
  have hd : coreClockFactor (coreRadius (y 0) (y 2)) (y 1) (y 3) ≠ 0 := by
    intro hd
    apply hrate
    change coreOriginalClockRate y = 0
    simp [coreOriginalClockRate, hd]
  have hpush : fderiv ℝ toProjectiveState X (normalizedField X) = projectiveOriginalField y := by
    have hs : 6 / projectiveStateDenom y = 1 + X 0 := projective_inverse_scale hA hc
    rw [toProjectiveState_fderiv_field hA hc]
    rw [projectiveOriginalField, hs]
  change fderiv ℝ toCoreAngleState y (fderiv ℝ toProjectiveState X
    (normalizedFlowDifferential x t₀ t v +
      (-(fderiv ℝ normalizedCoreAngle X (normalizedField X))⁻¹ *
        fderiv ℝ normalizedCoreAngle X (normalizedFlowDifferential x t₀ t v)) • normalizedField X)) = _
  rw [map_add, map_smul, map_add, map_smul, normalizedCoreAngle_fderiv_field hA hc hV,
    normalizedCoreAngle_fderiv hA hV, hpush, toCoreAngleState_fderiv_field hV hd]
  ext i
  simp only [coreClockProjection, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  change coreOriginalClockRate y ≠ 0 at hrate
  dsimp only [y, X] at hrate ⊢
  field_simp [hrate]
  ring

/-- A locally unique fixed-angle arrival, constructed from the actual normalized flow. -/
theorem exists_projectiveCoreAngle_event {y : ProjectiveState} {t₀ t : ℝ}
    (hD : 0 < projectiveStateDenom y) (ht : t ∈ normalizedMaxDomain (fromProjectiveState y) t₀)
    (hA : 0 < 1 + normalizedMaxCurve (fromProjectiveState y) t₀ t 0)
    (hV : 0 < projectiveOriginalFlow y t₀ t 2)
    (hrate : coreOriginalClockRate (projectiveOriginalFlow y t₀ t) ≠ 0) :
    ∃ τ : ProjectiveState → ℝ, τ y = t ∧ ContDiffAt ℝ 1 τ y ∧
      (∀ᶠ z in 𝓝 y, τ z ∈ normalizedMaxDomain (fromProjectiveState z) t₀ ∧
        0 < 1 + normalizedMaxCurve (fromProjectiveState z) t₀ (τ z) 0 ∧
        0 < projectiveOriginalFlow z t₀ (τ z) 2 ∧
        projectiveCoreAngle (projectiveOriginalFlow z t₀ (τ z)) =
          projectiveCoreAngle (projectiveOriginalFlow y t₀ t)) ∧
      (∀ᶠ z : ProjectiveState × ℝ in 𝓝 (y, t),
        z.2 ∈ normalizedMaxDomain (fromProjectiveState z.1) t₀ ∧
        (projectiveCoreAngle (projectiveOriginalFlow z.1 t₀ z.2) =
          projectiveCoreAngle (projectiveOriginalFlow y t₀ t) ↔ τ z.1 = z.2)) ∧
      ContDiffAt ℝ 1 (fun z => toCoreAngleState (projectiveOriginalFlow z t₀ (τ z))) y ∧
      HasFDerivAt (fun z => toCoreAngleState (projectiveOriginalFlow z t₀ (τ z)))
        (coreAngleArrivalDifferential y t₀ t) y := by
  let x := fromProjectiveState y
  let X := normalizedMaxCurve x t₀ t
  let b := toProjectiveState X
  have hc : stateConstraint X = 1 :=
    (normalizedMaxCurve_constraint ht).trans (fromProjectiveState_constraint (ne_of_gt hD))
  have htrans : normalizedEventRate normalizedCoreAngle x t₀ t ≠ 0 := by
    change fderiv ℝ normalizedCoreAngle X (normalizedField X) ≠ 0
    rw [normalizedCoreAngle_fderiv_field (ne_of_gt hA) hc hV]
    exact hrate
  obtain ⟨tau, hinit, hctau, _, hhit, huniq, hcmap, hdmap⟩ :=
    exists_normalized_event ht (contDiffAt_normalizedCoreAngle 1 (ne_of_gt hA) hV) htrans
  let τ : ProjectiveState → ℝ := fun z => tau (fromProjectiveState z)
  have hfrom := contDiffAt_fromProjectiveState 1 (ne_of_gt hD)
  have hfrom' := (hfrom.differentiableAt (by norm_num)).hasFDerivAt
  have hτ : τ y = t := hinit
  let eta : ProjectiveState → NormalizedState := fun z => normalizedMaxCurve (fromProjectiveState z) t₀ (τ z)
  have hceta : ContDiffAt ℝ 1 eta y := hcmap.comp y hfrom
  have heta : eta y = X := by change normalizedMaxCurve x t₀ (τ y) = X; rw [hτ]
  have hto : ContDiffAt ℝ 1 toProjectiveState (eta y) := by
    rw [heta]
    exact contDiffAt_toProjectiveState 1 (ne_of_gt hA)
  have hAnear : ∀ᶠ z in 𝓝 y, 0 < 1 + eta z 0 := by
    have H : ContinuousAt (fun z => 1 + eta z 0) y :=
      continuousAt_const.add ((continuous_apply 0).continuousAt.comp hceta.continuousAt)
    apply H.eventually (isOpen_Ioi.mem_nhds ?_)
    change 0 < 1 + eta y 0
    rw [heta]
    exact hA
  have hVnear : ∀ᶠ z in 𝓝 y, 0 < toProjectiveState (eta z) 2 := by
    apply ((continuous_apply 2).continuousAt.comp (hto.continuousAt.comp hceta.continuousAt)).eventually
      (isOpen_Ioi.mem_nhds ?_)
    change 0 < toProjectiveState (eta y) 2
    rw [heta]
    exact hV
  have hcCoord : ContDiffAt ℝ 1 (fun Z => toCoreAngleState (toProjectiveState Z))
      (normalizedMaxCurve x t₀ (tau x)) := by
    rw [hinit]
    exact (contDiffAt_toCoreAngleState 1 hV).comp X (contDiffAt_toProjectiveState 1 (ne_of_gt hA))
  have hdCoord : HasFDerivAt (fun Z => toCoreAngleState (toProjectiveState Z))
      ((fderiv ℝ toCoreAngleState b).comp (fderiv ℝ toProjectiveState X))
      (normalizedMaxCurve x t₀ (tau x)) := by
    rw [hinit]
    exact ((contDiffAt_toCoreAngleState 1 hV).differentiableAt (by norm_num)).hasFDerivAt.comp X
      ((contDiffAt_toProjectiveState 1 (ne_of_gt hA)).differentiableAt (by norm_num)).hasFDerivAt
  refine ⟨τ, hτ, hctau.comp y hfrom, ?_, ?_, ?_, ?_⟩
  · filter_upwards [hfrom.continuousAt.eventually hhit, hAnear, hVnear] with z hz hAz hVz
    exact ⟨hz.1, hAz, hVz, hz.2⟩
  · have hfamily : ContinuousAt (fun z : ProjectiveState × ℝ => (fromProjectiveState z.1, z.2))
        (y, t) := by
      convert! (hfrom.continuousAt.comp
        (continuousAt_fst : ContinuousAt (Prod.fst : ProjectiveState × ℝ → ProjectiveState) (y, t))).prodMk
          continuousAt_snd using 1
    exact hfamily.eventually huniq
  · convert! (hcCoord.comp x hcmap).comp y hfrom using 1
  · have H := (hdCoord.comp x hdmap).comp y hfrom'
    convert! H using 1
    apply ContinuousLinearMap.ext
    intro w
    exact (coreAngle_event_projection (ne_of_gt hA) hc hV hrate
      (fderiv ℝ fromProjectiveState y w)).symm

end BianchiIX
