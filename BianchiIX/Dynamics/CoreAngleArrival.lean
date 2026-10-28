import BianchiIX.Dynamics.CoreAngleCharts
import BianchiIX.Dynamics.CoreAngleEvents
import BianchiIX.Dynamics.CoreFlowGrowth

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

def scaleCoreVariationLinear (k : ℝ) : CoreAngleState →L[ℝ] CoreAngleState :=
  ContinuousLinearMap.pi ![ContinuousLinearMap.proj 0,
    k • ContinuousLinearMap.proj 1, ContinuousLinearMap.proj 2]

theorem scaleCoreVariationLinear_apply (k : ℝ) (v : CoreAngleState) :
    scaleCoreVariationLinear k v = scaleCoreVariation k v := by
  ext i
  fin_cases i <;> rfl

theorem scaleCoreVariation_inverse {k : ℝ} (hk : k ≠ 0) (v : CoreAngleState) :
    scaleCoreVariation k (scaleCoreVariation k⁻¹ v) = v := by
  ext i
  fin_cases i <;> simp [scaleCoreVariation, hk]

theorem core_weighted_opNorm_bound {L : CoreAngleState →L[ℝ] CoreAngleState} {k C : ℝ}
    (hk : k ≠ 0) (hC : 0 ≤ C)
    (hL : ∀ v, ‖scaleCoreVariation k (L v)‖ ≤ ‖scaleCoreVariation k v‖ * C) :
    ‖(scaleCoreVariationLinear k).comp (L.comp (scaleCoreVariationLinear k⁻¹))‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro v
  simpa only [ContinuousLinearMap.comp_apply, scaleCoreVariationLinear_apply,
    scaleCoreVariation_inverse hk, mul_comm] using hL (scaleCoreVariation k⁻¹ v)

def coreAngleSectionDifferential (z : ℝ) (Y : CoreAngleState) (t₀ t : ℝ) :
    CoreAngleState →L[ℝ] CoreAngleState :=
  (coreAngleArrivalDifferential (fromCoreAngleState z Y) t₀ t).comp
    (fderiv ℝ (fromCoreAngleState z) Y)

theorem coreAngleSectionDifferential_apply (z : ℝ) (Y : CoreAngleState) (t₀ t : ℝ)
    (v : CoreAngleState) :
    coreAngleSectionDifferential z Y t₀ t v =
      coreProjectedFlowVariation (fromCoreAngleState z Y) t₀ t
        (fderiv ℝ (fromCoreAngleState z) Y v) := rfl

theorem exists_coreAngle_section_event {z : ℝ} {Y : CoreAngleState} {t₀ t : ℝ}
    (hr : 0 < Y 0) (hD : 0 < projectiveStateDenom (fromCoreAngleState z Y))
    (ht : t ∈ normalizedMaxDomain (fromProjectiveState (fromCoreAngleState z Y)) t₀)
    (hA : 0 < 1 + normalizedMaxCurve (fromProjectiveState (fromCoreAngleState z Y)) t₀ t 0)
    (hV : 0 < projectiveOriginalFlow (fromCoreAngleState z Y) t₀ t 2)
    (hrate : coreOriginalClockRate (projectiveOriginalFlow (fromCoreAngleState z Y) t₀ t) ≠ 0) :
    ∃ τ : CoreAngleState → ℝ, τ Y = t ∧ ContDiffAt ℝ 1 τ Y ∧
      (∀ᶠ X in 𝓝 Y, τ X ∈ normalizedMaxDomain (fromProjectiveState (fromCoreAngleState z X)) t₀ ∧
        0 < 1 + normalizedMaxCurve (fromProjectiveState (fromCoreAngleState z X)) t₀ (τ X) 0 ∧
        0 < projectiveOriginalFlow (fromCoreAngleState z X) t₀ (τ X) 2 ∧
        projectiveCoreAngle (projectiveOriginalFlow (fromCoreAngleState z X) t₀ (τ X)) =
          projectiveCoreAngle (projectiveOriginalFlow (fromCoreAngleState z Y) t₀ t)) ∧
      (∀ᶠ q : CoreAngleState × ℝ in 𝓝 (Y, t),
        q.2 ∈ normalizedMaxDomain (fromProjectiveState (fromCoreAngleState z q.1)) t₀ ∧
        (projectiveCoreAngle (projectiveOriginalFlow (fromCoreAngleState z q.1) t₀ q.2) =
          projectiveCoreAngle (projectiveOriginalFlow (fromCoreAngleState z Y) t₀ t) ↔ τ q.1 = q.2)) ∧
      ContDiffAt ℝ 1 (fun X => toCoreAngleState (projectiveOriginalFlow (fromCoreAngleState z X) t₀ (τ X))) Y ∧
      HasFDerivAt (fun X => toCoreAngleState (projectiveOriginalFlow (fromCoreAngleState z X) t₀ (τ X)))
        (coreAngleSectionDifferential z Y t₀ t) Y := by
  obtain ⟨tau, hinit, hctau, hhit, huniq, hcmap, hdmap⟩ :=
    exists_projectiveCoreAngle_event hD ht hA hV hrate
  have hfrom := contDiffAt_fromCoreAngleState 1 z (ne_of_gt hr)
  refine ⟨fun X => tau (fromCoreAngleState z X), hinit, hctau.comp Y hfrom,
    hfrom.continuousAt.eventually hhit, ?_, ?_, ?_⟩
  · have hfamily : ContinuousAt (fun q : CoreAngleState × ℝ => (fromCoreAngleState z q.1, q.2))
        (Y, t) := by
      convert! (hfrom.continuousAt.comp
        (continuousAt_fst : ContinuousAt (Prod.fst : CoreAngleState × ℝ → CoreAngleState) (Y, t))).prodMk
          continuousAt_snd using 1
    exact hfamily.eventually huniq
  · convert! hcmap.comp Y hfrom using 1
  · exact hdmap.comp Y (hfrom.differentiableAt (by norm_num)).hasFDerivAt

theorem coreAngleSectionDifferential_bound {z k t₀ t : ℝ} {Y : CoreAngleState}
    (hk : 6 ≤ k) (hr : 0 < Y 0) (ht : t₀ ≤ t)
    (hD : 0 < projectiveStateDenom (fromCoreAngleState z Y))
    (hdomain : Icc t₀ t ⊆ normalizedMaxDomain (fromProjectiveState (fromCoreAngleState z Y)) t₀)
    (hA : ∀ s ∈ Icc t₀ t, 0 < 1 + normalizedMaxCurve (fromProjectiveState (fromCoreAngleState z Y)) t₀ s 0)
    (hregion : ∀ s ∈ Icc t₀ t, coreRegion k (projectiveOriginalFlow (fromCoreAngleState z Y) t₀ s))
    (v : CoreAngleState) :
    ‖scaleCoreVariation k (coreAngleSectionDifferential z Y t₀ t v)‖ ≤
      ‖scaleCoreVariation k v‖ * coreVariationBound := by
  have H := coreProjectedFlowVariation_growth hk ht hD hdomain hA hregion
    (fderiv ℝ (fromCoreAngleState z) Y v)
  rw [coreProjectedFlowVariation_initial hD, coreClockProjection_fromCoreAngleState z hr] at H
  exact H

theorem coreAngleSectionDifferential_opNorm {z k t₀ t : ℝ} {Y : CoreAngleState}
    (hk : 6 ≤ k) (hr : 0 < Y 0) (ht : t₀ ≤ t)
    (hD : 0 < projectiveStateDenom (fromCoreAngleState z Y))
    (hdomain : Icc t₀ t ⊆ normalizedMaxDomain (fromProjectiveState (fromCoreAngleState z Y)) t₀)
    (hA : ∀ s ∈ Icc t₀ t, 0 < 1 + normalizedMaxCurve (fromProjectiveState (fromCoreAngleState z Y)) t₀ s 0)
    (hregion : ∀ s ∈ Icc t₀ t, coreRegion k (projectiveOriginalFlow (fromCoreAngleState z Y) t₀ s)) :
    ‖(scaleCoreVariationLinear k).comp
      ((coreAngleSectionDifferential z Y t₀ t).comp (scaleCoreVariationLinear k⁻¹))‖ ≤ coreVariationBound :=
  core_weighted_opNorm_bound (by linarith only [hk]) (Real.exp_pos _).le
    (coreAngleSectionDifferential_bound hk hr ht hD hdomain hA hregion)

/-- The bound is on the derivative of the actual, locally unique fixed-angle arrival map. -/
theorem exists_coreAngle_arrival_bound {z k t₀ t : ℝ} {Y : CoreAngleState}
    (hk : 6 ≤ k) (hr : 0 < Y 0) (ht : t₀ ≤ t)
    (hD : 0 < projectiveStateDenom (fromCoreAngleState z Y))
    (hdomain : Icc t₀ t ⊆ normalizedMaxDomain (fromProjectiveState (fromCoreAngleState z Y)) t₀)
    (hA : ∀ s ∈ Icc t₀ t, 0 < 1 + normalizedMaxCurve (fromProjectiveState (fromCoreAngleState z Y)) t₀ s 0)
    (hregion : ∀ s ∈ Icc t₀ t, coreRegion k (projectiveOriginalFlow (fromCoreAngleState z Y) t₀ s)) :
    ∃ τ : CoreAngleState → ℝ, τ Y = t ∧ ContDiffAt ℝ 1 τ Y ∧
      (∀ᶠ X in 𝓝 Y, τ X ∈ normalizedMaxDomain (fromProjectiveState (fromCoreAngleState z X)) t₀ ∧
        0 < 1 + normalizedMaxCurve (fromProjectiveState (fromCoreAngleState z X)) t₀ (τ X) 0 ∧
        0 < projectiveOriginalFlow (fromCoreAngleState z X) t₀ (τ X) 2 ∧
        projectiveCoreAngle (projectiveOriginalFlow (fromCoreAngleState z X) t₀ (τ X)) =
          projectiveCoreAngle (projectiveOriginalFlow (fromCoreAngleState z Y) t₀ t)) ∧
      (∀ᶠ q : CoreAngleState × ℝ in 𝓝 (Y, t),
        q.2 ∈ normalizedMaxDomain (fromProjectiveState (fromCoreAngleState z q.1)) t₀ ∧
        (projectiveCoreAngle (projectiveOriginalFlow (fromCoreAngleState z q.1) t₀ q.2) =
          projectiveCoreAngle (projectiveOriginalFlow (fromCoreAngleState z Y) t₀ t) ↔ τ q.1 = q.2)) ∧
      ContDiffAt ℝ 1 (fun X => toCoreAngleState (projectiveOriginalFlow (fromCoreAngleState z X) t₀ (τ X))) Y ∧
      ‖(scaleCoreVariationLinear k).comp
        ((fderiv ℝ (fun X => toCoreAngleState (projectiveOriginalFlow (fromCoreAngleState z X) t₀ (τ X))) Y).comp
          (scaleCoreVariationLinear k⁻¹))‖ ≤ coreVariationBound := by
  have htmem : t ∈ Icc t₀ t := ⟨ht, le_rfl⟩
  obtain ⟨τ, hτ, hcτ, hhit, huniq, hcmap, hdmap⟩ := exists_coreAngle_section_event hr hD
    (hdomain htmem) (hA t htmem) (lt_of_lt_of_le zero_lt_one (hregion t htmem).2.1)
    (ne_of_gt (coreRegion_clock_regular hk (hregion t htmem)).2.2)
  refine ⟨τ, hτ, hcτ, hhit, huniq, hcmap, ?_⟩
  rw [hdmap.fderiv]
  exact coreAngleSectionDifferential_opNorm hk hr ht hD hdomain hA hregion

end BianchiIX
