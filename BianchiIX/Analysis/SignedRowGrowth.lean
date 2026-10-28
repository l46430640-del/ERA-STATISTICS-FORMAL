import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- The diagonal keeps its sign in the logarithmic bound for the supremum norm. -/
def signedRowSum (A : Matrix ι ι ℝ) (i : ι) : ℝ :=
  A i i + ∑ j ∈ Finset.univ.erase i, |A i j|

theorem norm_euler_le_of_signedRowSum {A : Matrix ι ι ℝ} {ρ h : ℝ}
    (hA : ∀ i, signedRowSum A i ≤ ρ) (hh : 0 ≤ h)
    (hdiag : ∀ i, 0 ≤ 1 + h * A i i) (x : ι → ℝ) :
    ‖x + h • A.mulVec x‖ ≤ (1 + h * ρ) * ‖x‖ := by
  apply (pi_norm_le_iff_of_nonempty _).mpr
  intro i
  have hcoord (j : ι) : |x j| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm x j
  have hsum : |∑ j ∈ Finset.univ.erase i, A i j * x j| ≤
      (∑ j ∈ Finset.univ.erase i, |A i j|) * ‖x‖ := by
    calc
      _ ≤ ∑ j ∈ Finset.univ.erase i, |A i j * x j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ Finset.univ.erase i, |A i j| * ‖x‖ := by
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hcoord j) (abs_nonneg _)
      _ = _ := (Finset.sum_mul _ _ _).symm
  have hid : (x + h • A.mulVec x) i =
      (1 + h * A i i) * x i + h * ∑ j ∈ Finset.univ.erase i, A i j * x j := by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct]
    rw [← Finset.add_sum_erase Finset.univ (fun j => A i j * x j) (Finset.mem_univ i)]
    ring
  rw [hid, Real.norm_eq_abs]
  calc
    _ ≤ |(1 + h * A i i) * x i| + |h * ∑ j ∈ Finset.univ.erase i, A i j * x j| := abs_add_le _ _
    _ = (1 + h * A i i) * |x i| + h * |∑ j ∈ Finset.univ.erase i, A i j * x j| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (hdiag i), abs_of_nonneg hh]
    _ ≤ (1 + h * A i i) * ‖x‖ + h * ((∑ j ∈ Finset.univ.erase i, |A i j|) * ‖x‖) :=
      add_le_add (mul_le_mul_of_nonneg_left (hcoord i) (hdiag i)) (mul_le_mul_of_nonneg_left hsum hh)
    _ = (1 + h * signedRowSum A i) * ‖x‖ := by unfold signedRowSum; ring
    _ ≤ (1 + h * ρ) * ‖x‖ := by
      exact mul_le_mul_of_nonneg_right (add_le_add (le_refl 1) (mul_le_mul_of_nonneg_left (hA i) hh)) (norm_nonneg _)

/-- The forward norm slope is controlled without differentiating the norm. -/
theorem norm_slope_right_le_of_signedRowSum {f : ℝ → (ι → ℝ)} {t ρ r : ℝ}
    {A : Matrix ι ι ℝ} (hf : HasDerivAt f (A.mulVec (f t)) t)
    (hA : ∀ i, signedRowSum A i ≤ ρ) (hr : ρ * ‖f t‖ < r) :
    ∀ᶠ s in 𝓝[>] t, (s - t)⁻¹ * (‖f s‖ - ‖f t‖) < r := by
  let e : ℝ → (ι → ℝ) := fun s => f s - (f t + (s - t) • A.mulVec (f t))
  have he : HasDerivAt e 0 t := by
    convert! hf.sub ((hasDerivAt_const t (f t)).add
      (((hasDerivAt_id t).sub_const t).smul_const (A.mulVec (f t)))) using 1
    simp
  have he0 : e t = 0 := by simp [e]
  have herr : ∀ᶠ s in 𝓝[>] t, ‖s - t‖⁻¹ * ‖e s - e t‖ < r - ρ * ‖f t‖ :=
    (he.hasDerivWithinAt (s := Ioi t)).limsup_norm_slope_le (by simpa using sub_pos.mpr hr)
  have hdiag : ∀ᶠ s in 𝓝 t, ∀ i, 0 ≤ 1 + (s - t) * A i i := by
    apply Filter.eventually_all.mpr
    intro i
    have hc : ContinuousAt (fun s : ℝ => 1 + (s - t) * A i i) t := by fun_prop
    exact (hc.eventually (isOpen_Ioi.mem_nhds (by simp))).mono fun _ hs => hs.le
  filter_upwards [herr, hdiag.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with s hs hd hst
  have hh : 0 < s - t := sub_pos.mpr hst
  rw [he0, sub_zero, Real.norm_eq_abs, abs_of_pos hh] at hs
  have hEuler := norm_euler_le_of_signedRowSum hA hh.le hd (f t)
  have H : ‖f s‖ - ‖f t‖ ≤ (s - t) * ρ * ‖f t‖ + ‖e s‖ := by
    have H' := norm_sub_norm_le (f s) (f t + (s - t) • A.mulVec (f t))
    change ‖f s‖ - ‖f t + (s - t) • A.mulVec (f t)‖ ≤ ‖e s‖ at H'
    nlinarith only [hEuler, H']
  have H' := mul_le_mul_of_nonneg_left H (inv_nonneg.mpr hh.le)
  have hid : (s - t)⁻¹ * ((s - t) * ρ * ‖f t‖ + ‖e s‖) =
      ρ * ‖f t‖ + (s - t)⁻¹ * ‖e s‖ := by field_simp
  rw [hid] at H'
  linarith only [H', hs]

theorem norm_le_initial_of_signedRowSum_nonpos {f : ℝ → (ι → ℝ)}
    {A : ℝ → Matrix ι ι ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b))
    (hderiv : ∀ t ∈ Ico a b, HasDerivAt f ((A t).mulVec (f t)) t)
    (hA : ∀ t ∈ Ico a b, ∀ i, signedRowSum (A t) i ≤ 0) :
    ∀ t ∈ Icc a b, ‖f t‖ ≤ ‖f a‖ := by
  intro t ht
  apply image_le_of_liminf_slope_right_le_deriv_boundary
    (continuous_norm.comp_continuousOn hf) (le_refl ‖f a‖) continuousOn_const
    (fun x _ => hasDerivWithinAt_const x (Ici x) ‖f a‖) ?_ ht
  intro x hx r hr
  have H := norm_slope_right_le_of_signedRowSum (hderiv x hx) (hA x hx) (by simpa using hr)
  simpa only [slope_def_module, smul_eq_mul, Function.comp_apply] using H.frequently

omit [Nonempty ι] in
theorem signedRowSum_sub_scalar {A : Matrix ι ι ℝ} (c : ℝ) (i : ι) :
    signedRowSum (A - c • (1 : Matrix ι ι ℝ)) i = signedRowSum A i - c := by
  have H : (∑ j ∈ Finset.univ.erase i, |(A - c • (1 : Matrix ι ι ℝ)) i j|) =
      ∑ j ∈ Finset.univ.erase i, |A i j| := by
    apply Finset.sum_congr rfl
    intro j hj
    have hij : i ≠ j := Ne.symm (Finset.mem_erase.mp hj).1
    simp [Matrix.sub_apply, Matrix.smul_apply, hij]
  unfold signedRowSum
  rw [H]
  simp [Matrix.sub_apply, Matrix.smul_apply]
  ring

theorem norm_le_exp_of_signedRowSum {f : ℝ → (ι → ℝ)}
    {A : ℝ → Matrix ι ι ℝ} {z z' : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b))
    (hderiv : ∀ t ∈ Ico a b, HasDerivAt f ((A t).mulVec (f t)) t)
    (hz : ContinuousOn z (Icc a b))
    (hzderiv : ∀ t ∈ Ico a b, HasDerivAt z (z' t) t)
    (hA : ∀ t ∈ Ico a b, ∀ i, signedRowSum (A t) i ≤ z' t) :
    ∀ t ∈ Icc a b, ‖f t‖ ≤ ‖f a‖ * Real.exp (z t - z a) := by
  let g : ℝ → (ι → ℝ) := fun t => Real.exp (-z t) • f t
  let B : ℝ → Matrix ι ι ℝ := fun t => A t - z' t • (1 : Matrix ι ι ℝ)
  have hg (t : ℝ) (ht : t ∈ Ico a b) : HasDerivAt g ((B t).mulVec (g t)) t := by
    convert! ((hzderiv t ht).neg.exp).smul (hderiv t ht) using 1
    dsimp [B, g]
    rw [Matrix.mulVec_smul, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
    ext i
    simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]
    ring
  have hB (t : ℝ) (ht : t ∈ Ico a b) (i : ι) : signedRowSum (B t) i ≤ 0 := by
    dsimp [B]
    rw [signedRowSum_sub_scalar]
    exact sub_nonpos.mpr (hA t ht i)
  have H := norm_le_initial_of_signedRowSum_nonpos
    ((Real.continuous_exp.comp_continuousOn hz.neg).smul hf) hg hB
  intro t ht
  have hn (s : ℝ) : ‖g s‖ = Real.exp (-z s) * ‖f s‖ := by
    simp only [g, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have H' := H t ht
  change ‖g t‖ ≤ ‖g a‖ at H'
  rw [hn, hn] at H'
  calc
    ‖f t‖ = Real.exp (z t) * (Real.exp (-z t) * ‖f t‖) := by
      rw [← mul_assoc, ← Real.exp_add]
      simp
    _ ≤ Real.exp (z t) * (Real.exp (-z a) * ‖f a‖) :=
      mul_le_mul_of_nonneg_left H' (Real.exp_pos _).le
    _ = ‖f a‖ * Real.exp (z t - z a) := by
      rw [← mul_assoc, ← Real.exp_add]
      simp only [sub_eq_add_neg, mul_comm]

end BianchiIX
