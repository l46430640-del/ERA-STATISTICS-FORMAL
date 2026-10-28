import BianchiIX.Dynamics.CoreTail
import BianchiIX.Dynamics.ReferenceShiftedVariation
import BianchiIX.Dynamics.ProjectiveFlowSecondRegularity

noncomputable section

namespace BianchiIX

open Set

theorem coreTailEntry_strong_fderiv {k : ℝ} (hk : 1 < k) :
    fderiv ℝ coreTailEntry ![k, 0, 0] (Pi.single 1 1) = Pi.single 1 1 := by
  have hline : HasDerivAt (fun a : ℝ => (![k, a, 0] : CoreAngleState)) (Pi.single 1 1) 0 := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · simpa using hasDerivAt_const (0 : ℝ) k
    · change HasDerivAt (fun a : ℝ => a) 1 0
      exact hasDerivAt_id' 0
    · simpa using hasDerivAt_const (0 : ℝ) (0 : ℝ)
  have hentry : HasDerivAt (fun a : ℝ => coreTailEntry ![k, a, 0]) (Pi.single 1 1) 0 := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · simpa [coreTailEntry] using hasDerivAt_const (0 : ℝ) (1 - Real.sqrt (k ^ 2 - 1))
    · change HasDerivAt (fun a : ℝ => a) 1 0
      exact hasDerivAt_id' 0
    · simpa [coreTailEntry] using hasDerivAt_const (0 : ℝ) (1 : ℝ)
    · simpa [coreTailEntry] using hasDerivAt_const (0 : ℝ) (0 : ℝ)
  exact (((contDiffAt_coreTailEntry 1 hk).differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt 0 hline).unique hentry

/-- The endpoint correction is tangent to the reference orbit and drops out of the energy first integral. -/
theorem coreTail_strong_variation_invariant {k η : ℝ} (hk : 1 < k) (hη : 0 < η ∧ η < 1) :
    let z := coreTailState η ![k, 0, 0]
    let v := fderiv ℝ (coreTailState η) ![k, 0, 0] (Pi.single 1 1)
    (z 0 - 1) * v 0 + z 2 * v 2 - 2 * z 2 * v 1 = -2 := by
  let Y : CoreAngleState := ![k, 0, 0]
  let s := referenceHalfTime k
  let t := referenceHeightTime k η
  let z := referencePulse k t
  let w : ProjectiveState := Pi.single 1 1
  let ξ := referenceShiftedVariation k s w t
  let a := fderiv ℝ (coreTailTime η) Y (Pi.single 1 1)
  have H := coreTail_reference_regular hk hη
  have hc : coreTailEntry Y = referencePulse k s := coreTailEntry_reference hk
  have hT : coreTailTime η Y = referenceShiftClock k s t := by
    rw [H.1]
    exact referencePulse_clock_integral k s t
  have hz : coreTailState η Y = z := by
    unfold coreTailState
    rw [hc, hT, referenceShiftClock_projective_orbit]
  have hD : 0 < projectiveStateDenom (coreTailEntry Y) := hc ▸ referencePulse_denom_pos k s
  have hdom : coreTailTime η Y ∈ normalizedMaxDomain (fromProjectiveState (coreTailEntry Y)) 0 := by
    rw [hc, hT]
    exact (referenceShiftClock_normalized_orbit k s t).1
  have hA : 0 < 1 + normalizedMaxCurve (fromProjectiveState (coreTailEntry Y)) 0 (coreTailTime η Y) 0 := by
    rw [hc, hT]
    exact referenceShiftClock_chart_pos k s t
  have hmap := (((contDiffAt_coreTailEntry 1 hk).differentiableAt (by norm_num)).hasFDerivAt).prodMk
    ((H.2.2.1.differentiableAt (by norm_num)).hasFDerivAt)
  have hflow := (hasFDerivAt_projectiveOriginalFlow hD hdom hA).comp Y hmap
  change HasFDerivAt (coreTailState η) _ Y at hflow
  have hv : fderiv ℝ (coreTailState η) Y (Pi.single 1 1) = ξ + a • projectiveOriginalField z := by
    rw [hflow.fderiv]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coprod_apply,
      ContinuousLinearMap.prod_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply,
      coreTailEntry_strong_fderiv hk]
    change projectiveFlowDifferential (coreTailEntry Y) 0 (coreTailTime η Y) w +
      a • projectiveOriginalField (coreTailState η Y) = _
    rw [hc, hT, hz]
    rfl
  have HI := referenceVariationInvariant_constant (I := univ) convex_univ
    (fun r _ => hasDerivAt_referenceShiftedVariation k s r w) (mem_univ s) (mem_univ t)
  rw [referenceShiftedVariation_initial] at HI
  dsimp only [referenceVariationInvariant] at HI
  rw [show referencePulse k s = ![1 - Real.sqrt (k ^ 2 - 1), 0, 1, 0] from referencePulse_exit hk] at HI
  change 2 * (z 0 - 1) * ξ 0 + 2 * z 2 * ξ 2 - 4 * z 2 * ξ 1 =
    2 * ((1 - Real.sqrt (k ^ 2 - 1)) - 1) * w 0 + 2 * 1 * w 2 - 4 * 1 * w 1 at HI
  norm_num [w, Pi.single_apply, show (2 : Fin 4) ≠ 1 by decide] at HI
  have HF : (z 0 - 1) * projectiveOriginalField z 0 + z 2 * projectiveOriginalField z 2 -
      2 * z 2 * projectiveOriginalField z 1 = 0 := by
    dsimp [z, referencePulse, projectiveOriginalField, projectiveField,
      phaseVelocity, activeVelocity, strongVelocity, coupling]
    ring
  change (coreTailState η Y 0 - 1) * fderiv ℝ (coreTailState η) Y (Pi.single 1 1) 0 +
    coreTailState η Y 2 * fderiv ℝ (coreTailState η) Y (Pi.single 1 1) 2 -
      2 * coreTailState η Y 2 * fderiv ℝ (coreTailState η) Y (Pi.single 1 1) 1 = -2
  rw [hz, hv]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination HI / 2 + a * HF

end BianchiIX
