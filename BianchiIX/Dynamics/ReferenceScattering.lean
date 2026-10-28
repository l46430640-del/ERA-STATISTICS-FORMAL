import BianchiIX.Dynamics.ReferenceVariation

noncomputable section

namespace BianchiIX

open Set

/-- A tangent forcing accounts for a change of the time coordinate. -/
def referenceVariationVelocity (k t : ℝ) (xi : ProjectiveState) (a : ℝ) : ProjectiveState :=
  fderiv ℝ projectiveField (referencePulse k t) xi + a • projectiveField (referencePulse k t)

theorem referenceVariationVelocity_eq (k t a : ℝ) (xi : ProjectiveState) :
    referenceVariationVelocity k t xi a =
      projectiveBoundaryVariation (referencePulse k t 0) (referencePulse k t 2) xi +
        a • projectiveField (referencePulse k t) := by
  unfold referenceVariationVelocity
  rw [show fderiv ℝ projectiveField (referencePulse k t) xi = _ from
    projectiveField_boundary_fderiv _ _ _]
  rfl

def referenceVariationInvariant (k t : ℝ) (xi : ProjectiveState) : ℝ :=
  2 * (referencePulse k t 0 - 1) * xi 0 + 2 * referencePulse k t 2 * xi 2 -
    4 * referencePulse k t 2 * xi 1

theorem hasDerivAt_referenceVariationInvariant {k t a : ℝ} {xi : ℝ → ProjectiveState}
    (hxi : HasDerivAt xi (referenceVariationVelocity k t (xi t) a) t) :
    HasDerivAt (fun s => referenceVariationInvariant k s (xi s)) 0 t := by
  have hm := hasDerivAt_pi.mp (hasDerivAt_referencePulse k t) 0
  have hv := hasDerivAt_pi.mp (hasDerivAt_referencePulse k t) 2
  have hx := hasDerivAt_pi.mp hxi
  have H := ((((hm.sub_const 1).const_mul 2).mul (hx 0)).add
    ((hv.const_mul 2).mul (hx 2))).sub ((hv.const_mul 4).mul (hx 1))
  convert! H using 1
  rw [referenceVariationVelocity_eq]
  dsimp [projectiveBoundaryVariation, referencePulse, projectiveField,
    phaseVelocity, strongVelocity, activeVelocity, weakVelocity, coupling]
  ring

theorem referenceVariationInvariant_constant {I : Set ℝ} (hI : Convex ℝ I)
    {k : ℝ} {xi : ℝ → ProjectiveState} {a : ℝ → ℝ}
    (hxi : ∀ t ∈ I, HasDerivAt xi (referenceVariationVelocity k t (xi t) (a t)) t)
    {s t : ℝ} (hs : s ∈ I) (ht : t ∈ I) :
    referenceVariationInvariant k t (xi t) = referenceVariationInvariant k s (xi s) := by
  have H := hI.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun u hu => (hasDerivAt_referenceVariationInvariant (hxi u hu)).hasDerivWithinAt)
    (C := 0) (fun _ _ => by simp) hs ht
  simpa [sub_eq_zero] using H

theorem referenceForcedVariation_transverse {I : Set ℝ} (hI : Convex ℝ I)
    {k : ℝ} {xi : ℝ → ProjectiveState} {a : ℝ → ℝ}
    (hxi : ∀ t ∈ I, HasDerivAt xi (referenceVariationVelocity k t (xi t) (a t)) t)
    {s t : ℝ} (hs : s ∈ I) (ht : t ∈ I) :
    xi t 1 = xi s 1 * (referenceTransverseMode k (k ^ 2 / 2) t /
      referenceTransverseMode k (k ^ 2 / 2) s) ∧
    xi t 3 = xi s 3 * (referenceTransverseMode k 2 t / referenceTransverseMode k 2 s) := by
  have hu (u : ℝ) (hu : u ∈ I) : HasDerivAt (fun v => xi v 1)
      (((1 - (referencePulse k u 0) ^ 2 - (referencePulse k u 2) ^ 2) / 2) * xi u 1) u := by
    have H := hasDerivAt_pi.mp (hxi u hu) 1
    rw [referenceVariationVelocity_eq] at H
    simpa [projectiveBoundaryVariation, projectiveField, strongVelocity, referencePulse] using H
  have hw (u : ℝ) (hu : u ∈ I) : HasDerivAt (fun v => xi v 3)
      ((-referencePulse k u 0 - 1) * xi u 3) u := by
    have H := hasDerivAt_pi.mp (hxi u hu) 3
    rw [referenceVariationVelocity_eq] at H
    simpa [projectiveBoundaryVariation, projectiveField, weakVelocity, referencePulse] using H
  exact ⟨homogeneous_solution_eq_mode_ratio hI hu (fun u _ => hasDerivAt_referenceStrongMode k u)
      (fun u _ => ne_of_gt (referenceTransverseMode_pos k (k ^ 2 / 2) u)) hs ht,
    homogeneous_solution_eq_mode_ratio hI hw (fun u _ => hasDerivAt_referenceWeakMode k u)
      (fun u _ => ne_of_gt (referenceTransverseMode_pos k 2 u)) hs ht⟩

def referenceExitProjection (k : ℝ) (xi : ProjectiveState) : ProjectiveState :=
  ![xi 0 - xi 2 / Real.sqrt (k ^ 2 - 1), xi 1, 0, xi 3]

theorem referenceCoreGap_pos {k : ℝ} (hk : 1 < k) : 0 < Real.sqrt (k ^ 2 - 1) :=
  Real.sqrt_pos.mpr (by nlinarith)

theorem referencePulse_exit_field {k : ℝ} (hk : 1 < k) :
    projectiveField (referencePulse k (referenceHalfTime k)) =
      ![-1, 0, -Real.sqrt (k ^ 2 - 1), 0] := by
  rw [referencePulse_exit hk]
  ext i
  fin_cases i <;>
    dsimp [projectiveField, phaseVelocity, strongVelocity, activeVelocity, weakVelocity, coupling] <;>
    ring

theorem referenceExitProjection_eq {k : ℝ} (hk : 1 < k) (xi : ProjectiveState) :
    referenceExitProjection k xi = xi -
      (xi 2 / projectiveField (referencePulse k (referenceHalfTime k)) 2) •
        projectiveField (referencePulse k (referenceHalfTime k)) := by
  rw [referencePulse_exit_field hk]
  have hd := ne_of_gt (referenceCoreGap_pos hk)
  ext i
  fin_cases i <;> dsimp [referenceExitProjection] <;> field_simp [hd] <;> ring

/-- The first integral eliminates both the phase quadrature and tangent time corrections. -/
theorem referenceVariation_scattering {I : Set ℝ} (hI : Convex ℝ I)
    {k : ℝ} (hk : 1 < k) {xi : ℝ → ProjectiveState} {a : ℝ → ℝ}
    (hxi : ∀ t ∈ I, HasDerivAt xi (referenceVariationVelocity k t (xi t) (a t)) t)
    (hin : -referenceHalfTime k ∈ I) (hout : referenceHalfTime k ∈ I)
    (hsection : xi (-referenceHalfTime k) 2 = 0) :
    referenceExitProjection k (xi (referenceHalfTime k)) =
      ![-xi (-referenceHalfTime k) 0 +
          (2 / Real.sqrt (k ^ 2 - 1)) * (1 - Real.exp (-k * Real.arcosh k)) *
            xi (-referenceHalfTime k) 1,
        Real.exp (-k * Real.arcosh k) * xi (-referenceHalfTime k) 1,
        0, Real.exp (-4 * Real.arcosh k / k) * xi (-referenceHalfTime k) 3] := by
  have he := referenceVariationInvariant_constant hI hxi hin hout
  have htw := referenceForcedVariation_transverse hI hxi hin hout
  rw [referenceStrongMode_ratio hk, referenceWeakMode_ratio] at htw
  dsimp [referenceVariationInvariant] at he
  rw [referencePulse_entry hk, referencePulse_exit hk] at he
  dsimp at he
  rw [hsection, htw.1] at he
  have hd := ne_of_gt (referenceCoreGap_pos hk)
  ext i
  fin_cases i
  · dsimp [referenceExitProjection]
    field_simp
    simp only [neg_mul] at he ⊢
    linear_combination -(1 / 2) * he
  · exact htw.1.trans (mul_comm _ _)
  · rfl
  · exact htw.2.trans (mul_comm _ _)

end BianchiIX
