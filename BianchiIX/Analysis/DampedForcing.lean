import BianchiIX.Analysis.SignedRowGrowth

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

theorem abs_slope_right_le_of_damping {f : ℝ → ℝ} {t d g B r : ℝ}
    (hf : HasDerivAt f (d * f t + g) t) (hd : d ≤ 0) (hg : |g| ≤ B) (hr : B < r) :
    ∀ᶠ s in 𝓝[>] t, (s - t)⁻¹ * (|f s| - |f t|) < r := by
  let e : ℝ → ℝ := fun s => f s - (f t + (s - t) * (d * f t + g))
  have he : HasDerivAt e 0 t := by
    convert! hf.sub ((hasDerivAt_const t (f t)).add
      (((hasDerivAt_id t).sub_const t).mul_const (d * f t + g))) using 1
    simp
  have he0 : e t = 0 := by simp [e]
  have herr : ∀ᶠ s in 𝓝[>] t, ‖s - t‖⁻¹ * ‖e s - e t‖ < r - B :=
    (he.hasDerivWithinAt (s := Ioi t)).limsup_norm_slope_le (by simpa using sub_pos.mpr hr)
  have hdiag : ∀ᶠ s in 𝓝 t, 0 ≤ 1 + (s - t) * d := by
    have hc : ContinuousAt (fun s : ℝ => 1 + (s - t) * d) t := by fun_prop
    exact (hc.eventually (isOpen_Ioi.mem_nhds (by simp))).mono fun _ h => h.le
  filter_upwards [herr, hdiag.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with s hs hdiag hst
  have hh : 0 < s - t := sub_pos.mpr hst
  rw [he0, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hh] at hs
  have hEuler : |f t + (s - t) * (d * f t + g)| ≤ |f t| + (s - t) * B := by
    rw [show f t + (s - t) * (d * f t + g) = (1 + (s - t) * d) * f t + (s - t) * g by ring]
    calc
      _ ≤ |(1 + (s - t) * d) * f t| + |(s - t) * g| := abs_add_le _ _
      _ = (1 + (s - t) * d) * |f t| + (s - t) * |g| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hdiag, abs_of_pos hh]
      _ ≤ |f t| + (s - t) * B := add_le_add
        (mul_le_of_le_one_left (abs_nonneg _) (by nlinarith only [hd, hh.le]))
        (mul_le_mul_of_nonneg_left hg hh.le)
  have hdiff := norm_sub_norm_le (f s) (f t + (s - t) * (d * f t + g))
  simp only [Real.norm_eq_abs] at hdiff
  change |f s| - |f t + (s - t) * (d * f t + g)| ≤ |e s| at hdiff
  have H : |f s| - |f t| ≤ (s - t) * B + |e s| := by linarith only [hdiff, hEuler]
  have H' := mul_le_mul_of_nonneg_left H (inv_nonneg.mpr hh.le)
  have hid : (s - t)⁻¹ * ((s - t) * B + |e s|) = B + (s - t)⁻¹ * |e s| := by field_simp
  rw [hid] at H'
  linarith only [H', hs]

/-- An arbitrary signed damping coefficient contributes no growth beyond the forcing primitive. -/
theorem abs_le_primitive_of_damping {f d g p p' : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b))
    (hdf : ∀ t ∈ Ico a b, HasDerivAt f (d t * f t + g t) t)
    (hp : ContinuousOn p (Icc a b)) (hdp : ∀ t ∈ Ico a b, HasDerivAt p (p' t) t)
    (hd : ∀ t ∈ Ico a b, d t ≤ 0) (hg : ∀ t ∈ Ico a b, |g t| ≤ p' t) :
    ∀ t ∈ Icc a b, |f t| ≤ |f a| + (p t - p a) := by
  intro t ht
  apply image_le_of_liminf_slope_right_le_deriv_boundary hf.abs (by simp) (continuousOn_const.add (hp.sub continuousOn_const))
    (fun s hs => ((hdp s hs).sub_const (p a)).const_add |f a| |>.hasDerivWithinAt) ?_ ht
  intro s hs r hr
  have H := abs_slope_right_le_of_damping (hdf s hs) (hd s hs) (hg s hs) hr
  simpa only [slope_def_module, smul_eq_mul] using H.frequently

/-- Exponentially decaying forcing with the same damping rate, in any nondecreasing clock. -/
theorem abs_le_affine_exp_of_clock_damping {f d g z z' : ℝ → ℝ} {a b c B : ℝ}
    (hf : ∀ t ∈ Icc a b, HasDerivAt f (z' t * (d t * f t + g t)) t)
    (hz : ∀ t ∈ Icc a b, HasDerivAt z (z' t) t)
    (hzpos : ∀ t ∈ Icc a b, 0 ≤ z' t)
    (hd : ∀ t ∈ Icc a b, d t ≤ -c)
    (hg : ∀ t ∈ Icc a b, |g t| ≤ B * Real.exp (-c * (z t - z a))) :
    ∀ t ∈ Icc a b, |f t| ≤ Real.exp (-c * (z t - z a)) * (|f a| + B * (z t - z a)) := by
  let e := fun t => Real.exp (c * (z t - z a))
  let F := fun t => e t * f t
  let D := fun t => z' t * (d t + c)
  let G := fun t => e t * z' t * g t
  let p := fun t => B * z t
  have he (t : ℝ) (ht : t ∈ Icc a b) : HasDerivAt e (e t * (c * z' t)) t := by
    convert! (((hz t ht).sub_const (z a)).const_mul c).exp using 1
  have hF (t : ℝ) (ht : t ∈ Icc a b) : HasDerivAt F (D t * F t + G t) t := by
    convert! (he t ht).mul (hf t ht) using 1
    dsimp [D, F, G]
    ring
  have hG (t : ℝ) (ht : t ∈ Icc a b) : |G t| ≤ B * z' t := by
    have hcancel : e t * Real.exp (-c * (z t - z a)) = 1 := by
      dsimp only [e]
      rw [← Real.exp_add]
      ring_nf
      exact Real.exp_zero
    calc
      |G t| = e t * z' t * |g t| := by
        dsimp [G]
        rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_nonneg (hzpos t ht)]
      _ ≤ e t * z' t * (B * Real.exp (-c * (z t - z a))) :=
        mul_le_mul_of_nonneg_left (hg t ht) (mul_nonneg (Real.exp_pos _).le (hzpos t ht))
      _ = B * z' t := by
        calc
          _ = B * z' t * (e t * Real.exp (-c * (z t - z a))) := by ring
          _ = _ := by rw [hcancel, mul_one]
  have H := abs_le_primitive_of_damping
    (fun t ht => (hF t ht).continuousAt.continuousWithinAt)
    (fun t ht => hF t (Ico_subset_Icc_self ht))
    (fun t ht => ((hz t ht).const_mul B).continuousAt.continuousWithinAt)
    (fun t ht => (hz t (Ico_subset_Icc_self ht)).const_mul B)
    (fun t ht => mul_nonpos_of_nonneg_of_nonpos (hzpos t (Ico_subset_Icc_self ht))
      (by linarith only [hd t (Ico_subset_Icc_self ht)]))
    (fun t ht => hG t (Ico_subset_Icc_self ht))
  intro t ht
  have H' := H t ht
  change |F t| ≤ |F a| + (p t - p a) at H'
  have hFa : F a = f a := by simp [F, e]
  rw [hFa] at H'
  have hFt : |F t| = e t * |f t| := by dsimp only [F]; rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  rw [hFt] at H'
  have hcancel : Real.exp (-c * (z t - z a)) * e t = 1 := by
    dsimp only [e]
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  have H'' := mul_le_mul_of_nonneg_left H' (Real.exp_pos (-c * (z t - z a))).le
  rw [← mul_assoc, hcancel, one_mul] at H''
  convert! H'' using 1
  dsimp [p]
  ring

end BianchiIX
