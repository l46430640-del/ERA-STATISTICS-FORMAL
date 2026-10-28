import BianchiIX.Dynamics.ReferenceShiftedVariation
import BianchiIX.Dynamics.EntranceRadiusCorrection

noncomputable section

namespace BianchiIX

open Set

theorem referencePulse_radius {k : ℝ} (hk : 0 ≤ k) (t : ℝ) :
    coreRadius (referencePulse k t 0) (referencePulse k t 2) = k := by
  rw [coreRadius, referencePulse_energy, Real.sqrt_sq hk]

theorem referencePulse_radius_fderiv {k : ℝ} (hk : 0 < k) (t : ℝ) (w : ProjectiveState) :
    fderiv ℝ (fun y : ProjectiveState => coreRadius (y 0) (y 2)) (referencePulse k t) w =
      ((referencePulse k t 0 - 1) * w 0 + referencePulse k t 2 * w 2) / k := by
  rw [(hasFDerivAt_coreRadius_state (referencePulse_active_pos hk t)).fderiv,
    referencePulse_radius hk.le]
  simp only [smul_apply, add_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
  ring

theorem referencePulse_radius_field {k : ℝ} (hk : 0 < k) (t : ℝ) :
    fderiv ℝ (fun y : ProjectiveState => coreRadius (y 0) (y 2)) (referencePulse k t)
      (projectiveField (referencePulse k t)) = 0 := by
  rw [referencePulse_radius_fderiv hk]
  dsimp [referencePulse, projectiveField, phaseVelocity, activeVelocity, coupling]
  ring

theorem referencePulse_strong_product (k s t : ℝ) :
    referencePulse k t 2 * (referenceTransverseMode k (k ^ 2 / 2) t /
      referenceTransverseMode k (k ^ 2 / 2) s) =
      referencePulse k s 2 * Real.exp (-(k ^ 2 / 2) * (t - s)) := by
  rw [show -(k ^ 2 / 2) * (t - s) = -(k ^ 2 / 2) * t - (-(k ^ 2 / 2) * s) by ring,
    Real.exp_sub]
  dsimp [referencePulse, referenceTransverseMode]
  field_simp

/-- The first integral gives the radial response on any reference segment,
including a tangent forcing caused by the original Einstein clock. -/
theorem referenceForcedVariation_radius {I : Set ℝ} (hI : Convex ℝ I)
    {k : ℝ} (hk : 0 < k) {xi : ℝ → ProjectiveState} {a : ℝ → ℝ}
    (hxi : ∀ t ∈ I, HasDerivAt xi (referenceVariationVelocity k t (xi t) (a t)) t)
    {s t : ℝ} (hs : s ∈ I) (ht : t ∈ I) :
    let R := fun y : ProjectiveState => coreRadius (y 0) (y 2)
    fderiv ℝ R (referencePulse k t) (xi t) = fderiv ℝ R (referencePulse k s) (xi s) +
      2 * referencePulse k s 2 * xi s 1 / k * (Real.exp (-(k ^ 2 / 2) * (t - s)) - 1) := by
  intro R
  have HI := referenceVariationInvariant_constant hI hxi hs ht
  have HU := (referenceForcedVariation_transverse hI hxi hs ht).1
  have HP : referencePulse k t 2 * xi t 1 =
      referencePulse k s 2 * xi s 1 * Real.exp (-(k ^ 2 / 2) * (t - s)) := by
    rw [HU, mul_left_comm, referencePulse_strong_product]
    ring
  dsimp only [referenceVariationInvariant] at HI
  rw [referencePulse_radius_fderiv hk, referencePulse_radius_fderiv hk]
  have HE : (referencePulse k t 0 - 1) * xi t 0 + referencePulse k t 2 * xi t 2 =
      (referencePulse k s 0 - 1) * xi s 0 + referencePulse k s 2 * xi s 2 +
        2 * referencePulse k s 2 * xi s 1 * (Real.exp (-(k ^ 2 / 2) * (t - s)) - 1) := by
    nlinarith only [HI, HP]
  rw [HE]
  ring

theorem referenceShiftedVariation_radius {k : ℝ} (hk : 0 < k) (s t : ℝ) (w : ProjectiveState) :
    let R := fun y : ProjectiveState => coreRadius (y 0) (y 2)
    fderiv ℝ R (referencePulse k t) (referenceShiftedVariation k s w t) =
      fderiv ℝ R (referencePulse k s) w +
        2 * referencePulse k s 2 * w 1 / k * (Real.exp (-(k ^ 2 / 2) * (t - s)) - 1) := by
  have H := referenceForcedVariation_radius (I := univ) convex_univ hk
    (fun r _ => hasDerivAt_referenceShiftedVariation k s r w) (mem_univ s) (mem_univ t)
  simpa only [referenceShiftedVariation_initial] using H

end BianchiIX
