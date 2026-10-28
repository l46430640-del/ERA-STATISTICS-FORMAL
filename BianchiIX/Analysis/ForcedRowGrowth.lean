import BianchiIX.Analysis.SignedRowGrowth
import Mathlib.Analysis.Calculus.Deriv.Prod

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem norm_slope_right_le_of_forced_signedRowSum {f : ℝ → (ι → ℝ)} {t ρ r : ℝ}
    {A : Matrix ι ι ℝ} {q : ι → ℝ} (hf : HasDerivAt f (A.mulVec (f t) + q) t)
    (hA : ∀ i, signedRowSum A i ≤ ρ) (hr : ρ * ‖f t‖ + ‖q‖ < r) :
    ∀ᶠ s in 𝓝[>] t, (s - t)⁻¹ * (‖f s‖ - ‖f t‖) < r := by
  let g : ℝ → (ι → ℝ) := fun s => f s - (s - t) • q
  have hgt : g t = f t := by simp [g]
  have hg : HasDerivAt g (A.mulVec (g t)) t := by
    rw [hgt]
    convert! hf.sub (((hasDerivAt_id t).sub_const t).smul_const q) using 1
    simp
  have H := norm_slope_right_le_of_signedRowSum hg hA
    (r := r - ‖q‖) (by rw [hgt]; linarith only [hr])
  filter_upwards [H, self_mem_nhdsWithin] with s hs hst
  have hh : 0 < s - t := sub_pos.mpr hst
  have hnorm : ‖f s‖ - ‖g s‖ ≤ (s - t) * ‖q‖ := by
    have H' := norm_sub_norm_le (f s) (g s)
    have heq : f s - g s = (s - t) • q := by dsimp [g]; abel
    rwa [heq, norm_smul, Real.norm_eq_abs, abs_of_pos hh] at H'
  have H' := mul_le_mul_of_nonneg_left hnorm (inv_nonneg.mpr hh.le)
  have hid : (s - t)⁻¹ * ((s - t) * ‖q‖) = ‖q‖ := by field_simp
  rw [hid] at H'
  rw [hgt] at hs
  nlinarith only [hs, H']

theorem norm_le_of_forced_signedRowSum_nonpos {f q : ℝ → (ι → ℝ)}
    {A : ℝ → Matrix ι ι ℝ} {B B' : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b))
    (hderiv : ∀ t ∈ Ico a b, HasDerivAt f ((A t).mulVec (f t) + q t) t)
    (hA : ∀ t ∈ Ico a b, ∀ i, signedRowSum (A t) i ≤ 0)
    (hB : ContinuousOn B (Icc a b)) (hB' : ∀ t ∈ Ico a b, HasDerivAt B (B' t) t)
    (hinit : ‖f a‖ ≤ B a) (hq : ∀ t ∈ Ico a b, ‖q t‖ ≤ B' t) :
    ∀ t ∈ Icc a b, ‖f t‖ ≤ B t := by
  apply image_le_of_liminf_slope_right_le_deriv_boundary
    (continuous_norm.comp_continuousOn hf) hinit hB (fun t ht => (hB' t ht).hasDerivWithinAt)
  intro t ht r hr
  have H := norm_slope_right_le_of_forced_signedRowSum (hderiv t ht) (hA t ht)
    (r := r) (by simpa only [zero_mul, zero_add] using (hq t ht).trans_lt hr)
  simpa only [slope_def_module, smul_eq_mul, Function.comp_apply] using H.frequently

theorem abs_le_of_forced_nonpos {f q c B B' : ℝ → ℝ} {a b : ℝ}
    (hf : ∀ t ∈ Icc a b, HasDerivAt f (q t * f t + c t) t)
    (hq : ∀ t ∈ Icc a b, q t ≤ 0)
    (hB : ∀ t ∈ Icc a b, HasDerivAt B (B' t) t)
    (hinit : |f a| ≤ B a) (hc : ∀ t ∈ Icc a b, |c t| ≤ B' t) :
    ∀ t ∈ Icc a b, |f t| ≤ B t := by
  let F : ℝ → (Unit → ℝ) := fun t _ => f t
  let A : ℝ → Matrix Unit Unit ℝ := fun t _ _ => q t
  let C : ℝ → (Unit → ℝ) := fun t _ => c t
  have hF (t : ℝ) (ht : t ∈ Icc a b) : HasDerivAt F ((A t).mulVec (F t) + C t) t := by
    apply hasDerivAt_pi.mpr
    intro i
    simpa [A, F, C, Matrix.mulVec, dotProduct] using hf t ht
  have H := norm_le_of_forced_signedRowSum_nonpos (HasDerivAt.continuousOn hF)
    (fun t ht => hF t (Ico_subset_Icc_self ht))
    (fun t ht i => by simpa [A, signedRowSum] using hq t (Ico_subset_Icc_self ht))
    (HasDerivAt.continuousOn hB) (fun t ht => hB t (Ico_subset_Icc_self ht))
    (by simpa [F, Real.norm_eq_abs] using hinit)
    (fun t ht => by simpa [C, Real.norm_eq_abs] using hc t (Ico_subset_Icc_self ht))
  simpa [F, Real.norm_eq_abs] using H

end BianchiIX
