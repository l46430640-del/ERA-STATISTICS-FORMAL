import BianchiIX.Statistics.GaussTransport

/-! Exact cylinder length and the uniform density comparison in Section 3.4. -/

namespace BianchiIX

noncomputable section

open Set MeasureTheory
open scoped ENNReal

def gaussPrefixLength (a : ℕ → ℕ+) (n : ℕ) : ℝ :=
  1 / ((gaussDenoms a n).1 * ((gaussDenoms a n).1 + (gaussDenoms a n).2))

theorem gaussPrefixLength_pos (a : ℕ → ℕ+) (n : ℕ) : 0 < gaussPrefixLength a n := by
  have h := gaussDenoms_bounds a n
  have hq : 0 < (gaussDenoms a n).1 := by linarith [h.1]
  have hp := h.2.1
  unfold gaussPrefixLength
  positivity

private def densityPrimitive (q p x : ℝ) : ℝ := x / (q * (q + p * x))

private theorem hasDerivAt_densityPrimitive {q p x : ℝ}
    (hq : 0 < q) (hp : 0 ≤ p) (hx : 0 ≤ x) :
    HasDerivAt (densityPrimitive q p) (1 / (q + p * x) ^ 2) x := by
  have hd : 0 < q + p * x := by positivity
  have h := (hasDerivAt_id x).div
    ((((hasDerivAt_id x).const_mul p).const_add q).const_mul q) (mul_pos hq hd).ne'
  convert! h using 1
  dsimp only [id_eq]
  field_simp
  ring

private theorem densityPrimitive_strictMonoOn {q p : ℝ} (hq : 0 < q) (hp : 0 ≤ p) :
    StrictMonoOn (densityPrimitive q p) (Ici 0) := by
  intro x hx y hy hxy
  change 0 ≤ x at hx
  change 0 ≤ y at hy
  have hdx : 0 < q * (q + p * x) := by positivity
  have hdy : 0 < q * (q + p * y) := by positivity
  apply (div_lt_div_iff₀ hdx hdy).mpr
  nlinarith [mul_pos (sq_pos_of_pos hq) (sub_pos.mpr hxy)]

theorem volume_gaussCylinder_prefix (a : ℕ → ℕ+) (n : ℕ) :
    volume (gaussCylinder (digitPrefix a n)) = ENNReal.ofReal (gaussPrefixLength a n) := by
  let q := (gaussDenoms a n).1
  let p := (gaussDenoms a n).2
  have hq : 0 < q := by dsimp [q]; linarith [(gaussDenoms_bounds a n).1]
  have hp : 0 ≤ p := (gaussDenoms_bounds a n).2.1
  have hf (x : ℝ) (hx : 0 ≤ x) := hasDerivAt_densityPrimitive hq hp hx
  have hcont : ContinuousOn (densityPrimitive q p) (Icc 0 1) :=
    fun x hx => (hf x hx.1).continuousAt.continuousWithinAt
  have hmono := densityPrimitive_strictMonoOn hq hp
  have himg := hcont.image_Ioo_of_strictMonoOn zero_le_one (hmono.mono Icc_subset_Ici_self)
  have hG := volume_image_eq_lintegral_abs_deriv measurableSet_Ioo
    (fun x (hx : x ∈ Ioo (0 : ℝ) 1) =>
      (hasDerivAt_gaussWord_prefix a n hx.1.le).differentiableAt.hasDerivAt)
    (measurableEmbedding_gaussWord _).injective.injOn
  change volume (gaussWord (digitPrefix a n) '' Ioo 0 1) = _
  rw [hG]
  have heq : (∫⁻ x in Ioo (0 : ℝ) 1,
      ENNReal.ofReal |deriv (gaussWord (digitPrefix a n)) x|) =
      ∫⁻ x in Ioo (0 : ℝ) 1, ENNReal.ofReal |1 / (q + p * x) ^ 2| := by
    apply lintegral_congr_ae
    apply ae_restrict_of_forall_mem measurableSet_Ioo
    intro x hx
    dsimp only
    rw [abs_deriv_gaussWord_prefix a n hx.1.le, abs_of_nonneg (by positivity)]
    rfl
  rw [heq, ← volume_image_eq_lintegral_abs_deriv measurableSet_Ioo
    (fun x (hx : x ∈ Ioo (0 : ℝ) 1) => hf x hx.1.le)
    (hmono.injOn.mono (fun _ ht => ht.1.le)), himg, Real.volume_Ioo]
  simp [densityPrimitive, gaussPrefixLength, q, p]

theorem gaussPrefix_density_bounds (a : ℕ → ℕ+) (n : ℕ)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    (1 / 2) * gaussPrefixLength a n ≤ |deriv (gaussWord (digitPrefix a n)) x| ∧
      |deriv (gaussWord (digitPrefix a n)) x| ≤ 2 * gaussPrefixLength a n := by
  let q := (gaussDenoms a n).1
  let p := (gaussDenoms a n).2
  let D := q + p * x
  have h := gaussDenoms_bounds a n
  have hq : 0 < q := by dsimp [q]; linarith [h.1]
  have hp : 0 ≤ p := h.2.1
  have hpq : p ≤ q := h.2.2
  have hDlo : q ≤ D := by dsimp [D]; nlinarith [mul_nonneg hp hx.1]
  have hDhi : D ≤ q + p := by dsimp [D]; nlinarith [mul_nonneg hp (sub_nonneg.mpr hx.2)]
  have hDpos : 0 < D := hq.trans_le hDlo
  have hQpos : 0 < q * (q + p) := by positivity
  have hupper : q * (q + p) ≤ 2 * D ^ 2 := by
    have hs := mul_nonneg (sub_nonneg.mpr hDlo) (show 0 ≤ D + q by positivity)
    nlinarith [mul_nonneg hq.le (sub_nonneg.mpr hpq)]
  have hlower : D ^ 2 ≤ 2 * (q * (q + p)) := by
    have hs := mul_nonneg (sub_nonneg.mpr hDhi) (show 0 ≤ q + p + D by positivity)
    nlinarith [mul_nonneg (sub_nonneg.mpr hpq) (show 0 ≤ q + p by positivity)]
  have hu : 1 / D ^ 2 ≤ 2 / (q * (q + p)) :=
    (div_le_div_iff₀ (sq_pos_of_pos hDpos) hQpos).mpr (by simpa using hupper)
  have hl : 1 / (q * (q + p)) ≤ 2 / D ^ 2 :=
    (div_le_div_iff₀ hQpos (sq_pos_of_pos hDpos)).mpr (by simpa using hlower)
  rw [abs_deriv_gaussWord_prefix a n hx.1]
  change (1 / 2) * (1 / (q * (q + p))) ≤ 1 / D ^ 2 ∧
    1 / D ^ 2 ≤ 2 * (1 / (q * (q + p)))
  simp only [div_eq_mul_inv, one_mul] at hl hu ⊢
  constructor <;> linarith

theorem gaussPrefix_small_set_image_le (a : ℕ → ℕ+) (n : ℕ) {A : Set ℝ}
    (hA : MeasurableSet A) (hAsub : A ⊆ Ioo (0 : ℝ) 1) :
    volume (gaussWord (digitPrefix a n) '' A) ≤
      2 * volume (gaussCylinder (digitPrefix a n)) * volume A := by
  rw [volume_image_eq_lintegral_abs_deriv hA
    (fun x hx => (hasDerivAt_gaussWord_prefix a n (hAsub hx).1.le).differentiableAt.hasDerivAt)
    (measurableEmbedding_gaussWord _).injective.injOn, volume_gaussCylinder_prefix]
  calc
    (∫⁻ x in A, ENNReal.ofReal |deriv (gaussWord (digitPrefix a n)) x|) ≤
        ∫⁻ _ in A, ENNReal.ofReal (2 * gaussPrefixLength a n) := by
      apply lintegral_mono_ae
      apply ae_restrict_of_forall_mem hA
      intro x hx
      exact ENNReal.ofReal_le_ofReal (gaussPrefix_density_bounds a n
        ⟨(hAsub hx).1.le, (hAsub hx).2.le⟩).2
    _ = _ := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num

end

end BianchiIX
