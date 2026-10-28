import BianchiIX.Dynamics.ReferenceReturn
import BianchiIX.Dynamics.ProjectiveLinearization

noncomputable section

namespace BianchiIX

open Set

def referenceTransverseMode (k r t : ℝ) : ℝ :=
  Real.exp (-r * t) * Real.cosh (k * t)

theorem referenceTransverseMode_pos (k r t : ℝ) : 0 < referenceTransverseMode k r t :=
  mul_pos (Real.exp_pos _) (Real.cosh_pos _)

theorem hasDerivAt_referenceTransverseMode (k r t : ℝ) :
    HasDerivAt (referenceTransverseMode k r)
      ((-r + k * Real.tanh (k * t)) * referenceTransverseMode k r t) t := by
  have hz := (hasDerivAt_id t).const_mul k
  have hr := (hasDerivAt_id t).const_mul (-r)
  convert! hr.exp.mul hz.cosh using 1
  dsimp [referenceTransverseMode]
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp

theorem referencePulse_strong_coefficient (k t : ℝ) :
    (1 - (referencePulse k t 0) ^ 2 - (referencePulse k t 2) ^ 2) / 2 =
      -(k ^ 2 / 2) + k * Real.tanh (k * t) := by
  have he := referencePulse_energy k t
  dsimp [coreEnergy, referencePulse] at *
  nlinarith only [he]

theorem hasDerivAt_referenceStrongMode (k t : ℝ) :
    HasDerivAt (referenceTransverseMode k (k ^ 2 / 2))
      (((1 - (referencePulse k t 0) ^ 2 - (referencePulse k t 2) ^ 2) / 2) *
        referenceTransverseMode k (k ^ 2 / 2) t) t := by
  rw [referencePulse_strong_coefficient]
  exact hasDerivAt_referenceTransverseMode k (k ^ 2 / 2) t

theorem hasDerivAt_referenceWeakMode (k t : ℝ) :
    HasDerivAt (referenceTransverseMode k 2)
      ((-referencePulse k t 0 - 1) * referenceTransverseMode k 2 t) t := by
  convert! hasDerivAt_referenceTransverseMode k 2 t using 1
  dsimp [referencePulse]
  ring

/-- Division by a nonzero fundamental solution gives every scalar solution. -/
theorem homogeneous_solution_eq_mode_ratio {I : Set ℝ} (hI : Convex ℝ I)
    {f g a : ℝ → ℝ} (hf : ∀ t ∈ I, HasDerivAt f (a t * f t) t)
    (hg : ∀ t ∈ I, HasDerivAt g (a t * g t) t) (hzero : ∀ t ∈ I, g t ≠ 0)
    {s t : ℝ} (hs : s ∈ I) (ht : t ∈ I) : f t = f s * (g t / g s) := by
  have hq (u : ℝ) (hu : u ∈ I) : HasDerivAt (fun v => f v / g v) 0 u := by
    convert! (hf u hu).div (hg u hu) (hzero u hu) using 1
    ring
  have H := hI.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun u hu => (hq u hu).hasDerivWithinAt) (C := 0) (fun _ _ => by simp) hs ht
  have heq : f t / g t = f s / g s := by simpa [sub_eq_zero] using H
  rw [← mul_div_assoc]
  exact (eq_div_iff (hzero s hs)).mpr ((div_eq_div_iff (hzero t ht) (hzero s hs)).mp heq)

theorem referenceTransverseMode_ratio (k r h : ℝ) :
    referenceTransverseMode k r h / referenceTransverseMode k r (-h) = Real.exp (-2 * r * h) := by
  unfold referenceTransverseMode
  simp only [mul_neg, Real.cosh_neg]
  rw [mul_div_mul_right _ _ (ne_of_gt (Real.cosh_pos (k * h))), ← Real.exp_sub]
  congr 1
  ring

theorem referenceStrongMode_ratio {k : ℝ} (hk : 1 < k) :
    referenceTransverseMode k (k ^ 2 / 2) (referenceHalfTime k) /
      referenceTransverseMode k (k ^ 2 / 2) (-referenceHalfTime k) =
      Real.exp (-k * Real.arcosh k) := by
  rw [referenceTransverseMode_ratio]
  congr 1
  unfold referenceHalfTime
  field_simp [ne_of_gt (lt_trans zero_lt_one hk)]

theorem referenceWeakMode_ratio (k : ℝ) :
    referenceTransverseMode k 2 (referenceHalfTime k) /
      referenceTransverseMode k 2 (-referenceHalfTime k) =
      Real.exp (-4 * Real.arcosh k / k) := by
  rw [referenceTransverseMode_ratio]
  congr 1
  unfold referenceHalfTime
  ring

theorem referenceTransverseMultipliers_lt_one {k : ℝ} (hk : 1 < k) :
    Real.exp (-k * Real.arcosh k) ∈ Ioo 0 1 ∧
    Real.exp (-4 * Real.arcosh k / k) ∈ Ioo 0 1 := by
  have hk0 : 0 < k := lt_trans zero_lt_one hk
  have hL : 0 < Real.arcosh k := Real.arcosh_pos hk
  exact ⟨⟨Real.exp_pos _, Real.exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos (neg_neg_of_pos hk0) hL)⟩,
    ⟨Real.exp_pos _, Real.exp_lt_one_iff.mpr (div_neg_of_neg_of_pos (by linarith) hk0)⟩⟩

theorem referenceVariation_transverse {I : Set ℝ} (hI : Convex ℝ I)
    {k : ℝ} {xi : ℝ → ProjectiveState}
    (hxi : ∀ t ∈ I, HasDerivAt xi (fderiv ℝ projectiveField (referencePulse k t) (xi t)) t)
    {s t : ℝ} (hs : s ∈ I) (ht : t ∈ I) :
    xi t 1 = xi s 1 * (referenceTransverseMode k (k ^ 2 / 2) t /
      referenceTransverseMode k (k ^ 2 / 2) s) ∧
    xi t 3 = xi s 3 * (referenceTransverseMode k 2 t / referenceTransverseMode k 2 s) := by
  have hlin (u : ℝ) : fderiv ℝ projectiveField (referencePulse k u) (xi u) =
      projectiveBoundaryVariation (referencePulse k u 0) (referencePulse k u 2) (xi u) :=
    projectiveField_boundary_fderiv _ _ _
  have hu (u : ℝ) (hu : u ∈ I) : HasDerivAt (fun v => xi v 1)
      (((1 - (referencePulse k u 0) ^ 2 - (referencePulse k u 2) ^ 2) / 2) * xi u 1) u := by
    have H := hasDerivAt_pi.mp (hxi u hu) 1
    rw [hlin] at H
    exact H
  have hw (u : ℝ) (hu : u ∈ I) : HasDerivAt (fun v => xi v 3)
      ((-referencePulse k u 0 - 1) * xi u 3) u := by
    have H := hasDerivAt_pi.mp (hxi u hu) 3
    rw [hlin] at H
    exact H
  exact ⟨homogeneous_solution_eq_mode_ratio hI hu (fun u _ => hasDerivAt_referenceStrongMode k u)
      (fun u _ => ne_of_gt (referenceTransverseMode_pos k (k ^ 2 / 2) u)) hs ht,
    homogeneous_solution_eq_mode_ratio hI hw (fun u _ => hasDerivAt_referenceWeakMode k u)
      (fun u _ => ne_of_gt (referenceTransverseMode_pos k 2 u)) hs ht⟩

theorem referenceVariation_transverse_multipliers {I : Set ℝ} (hI : Convex ℝ I)
    {k : ℝ} (hk : 1 < k) {xi : ℝ → ProjectiveState}
    (hxi : ∀ t ∈ I, HasDerivAt xi (fderiv ℝ projectiveField (referencePulse k t) (xi t)) t)
    (hin : -referenceHalfTime k ∈ I) (hout : referenceHalfTime k ∈ I) :
    xi (referenceHalfTime k) 1 = xi (-referenceHalfTime k) 1 * Real.exp (-k * Real.arcosh k) ∧
    xi (referenceHalfTime k) 3 = xi (-referenceHalfTime k) 3 * Real.exp (-4 * Real.arcosh k / k) := by
  simpa only [referenceStrongMode_ratio hk, referenceWeakMode_ratio] using
    referenceVariation_transverse hI hxi hin hout

end BianchiIX
