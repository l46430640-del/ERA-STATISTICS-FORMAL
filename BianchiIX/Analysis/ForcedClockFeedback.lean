import BianchiIX.Analysis.CoupledClockVariation

noncomputable section

namespace BianchiIX

open Set MeasureTheory

/-- Zero initial phase with a continuous external source is absorbed by the same feedback kernel. -/
theorem forced_clock_feedback_bounds
    {Z q l g : ℝ → ℝ} {f : ℝ → Fin 2 → ℝ} {c : ℝ → Fin 3 → ℝ} {s t C A B Λ : ℝ}
    (hst : s ≤ t) (hC : 0 ≤ C) (hA : 0 ≤ A)
    (hZ : ∀ r ∈ Icc s t, HasDerivAt Z
      (q r * (c r 0 * Z r + c r 1 * f r 0 + c r 2 * f r 1 + g r)) r)
    (hZs : Z s = 0)
    (hl : ∀ r ∈ Icc s t, HasDerivAt l (q r) r) (hls : l s = 0)
    (hqc : ContinuousOn q (Icc s t)) (hq : ∀ r ∈ Icc s t, 0 ≤ q r)
    (hcc : ContinuousOn c (Icc s t)) (hgc : ContinuousOn g (Icc s t))
    (htrans : ∀ r ∈ Icc s t, |f r 0| + |f r 1| ≤ C * (A + ∫ z in s..r, |Z z| * q z))
    (hsource : (∫ r in s..t, (|g r| + C * A * (|c r 1| + |c r 2|)) * q r) ≤ B)
    (hbudget : (∫ r in s..t, coupledVariationFeedback C (l r) (c r) * q r) ≤ Λ)
    (hΛ : Λ ≤ 1 / 2) :
    ∀ r ∈ Icc s t, |Z r| ≤ 2 * B ∧ |f r 0| + |f r 1| ≤ C * (A + 2 * l r * B) := by
  let e := fun r => (|g r| + C * A * (|c r 1| + |c r 2|)) * q r
  let K := fun r => coupledVariationFeedback C (l r) (c r) * q r
  have hc (i : Fin 3) := (continuous_apply i).comp_continuousOn hcc
  have he : ContinuousOn e (Icc s t) :=
    (hgc.abs.add (((hc 1).abs.add (hc 2).abs).const_mul (C * A))).mul hqc
  have hK : ContinuousOn K (Icc s t) :=
    (((hc 0).abs.add ((HasDerivAt.continuousOn hl).mul ((hc 1).abs.add (hc 2).abs))).const_mul (C + 1)).mul hqc
  have hclock (r : ℝ) (hr : r ∈ Icc s t) : (∫ z in s..r, q z) = l r := by
    have hsub : Icc s r ⊆ Icc s t := Icc_subset_Icc_right hr.2
    have H := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun z hz => hl z (hsub ((uIcc_of_le hr.1) ▸ hz)))
      ((hqc.mono hsub).intervalIntegrable_of_Icc hr.1)
    simpa only [hls, sub_zero] using H
  have hl0 (r : ℝ) (hr : r ∈ Icc s t) : 0 ≤ l r := by
    rw [← hclock r hr]
    exact intervalIntegral.integral_nonneg hr.1 (fun z hz => hq z ⟨hz.1, hz.2.trans hr.2⟩)
  have he0 (r : ℝ) (hr : r ∈ Icc s t) : 0 ≤ e r := by dsimp [e]; positivity [hq r hr]
  have hK0 (r : ℝ) (hr : r ∈ Icc s t) : 0 ≤ K r := by
    dsimp [K, coupledVariationFeedback]
    positivity [hq r hr, hl0 r hr]
  have hcap (Q : ℝ) (hbound : ∀ r ∈ Icc s t, |Z r| ≤ Q) (r : ℝ) (hr : r ∈ Icc s t) :
      |f r 0| + |f r 1| ≤ C * (A + l r * Q) := by
    have hsub : Icc s r ⊆ Icc s t := Icc_subset_Icc_right hr.2
    have HI := intervalIntegral.integral_mono_on (μ := volume) hr.1
      ((((HasDerivAt.continuousOn hZ).abs.mul hqc).mono hsub).intervalIntegrable_of_Icc hr.1)
      (((hqc.const_mul Q).mono hsub).intervalIntegrable_of_Icc hr.1)
      (fun z hz => mul_le_mul_of_nonneg_right (hbound z (hsub hz)) (hq z (hsub hz)))
    rw [intervalIntegral.integral_const_mul, hclock r hr] at HI
    simp only [Pi.mul_apply] at HI
    exact (htrans r hr).trans (mul_le_mul_of_nonneg_left (by nlinarith only [HI]) hC)
  have hfeedback (Q : ℝ) (hQ : 0 ≤ Q) (hbound : ∀ r ∈ Icc s t, |Z r| ≤ Q)
      (r : ℝ) (hr : r ∈ Icc s t) :
      |q r * (c r 0 * Z r + c r 1 * f r 0 + c r 2 * f r 1 + g r)| ≤ e r + K r * Q := by
    let R := C * (A + l r * Q)
    have HR := hcap Q hbound r hr
    have hx : |f r 0| ≤ R := by linarith only [HR, abs_nonneg (f r 1)]
    have hy : |f r 1| ≤ R := by linarith only [HR, abs_nonneg (f r 0)]
    have HT : |c r 0 * Z r + c r 1 * f r 0 + c r 2 * f r 1 + g r| ≤
        |g r| + |c r 0| * Q + (|c r 1| + |c r 2|) * R := by
      calc
        _ ≤ |c r 0 * Z r| + |c r 1 * f r 0| + |c r 2 * f r 1| + |g r| :=
          (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)
        _ ≤ |c r 0| * Q + |c r 1| * R + |c r 2| * R + |g r| := by
          simp only [abs_mul]
          exact add_le_add (add_le_add (add_le_add (mul_le_mul_of_nonneg_left (hbound r hr) (abs_nonneg _))
            (mul_le_mul_of_nonneg_left hx (abs_nonneg _))) (mul_le_mul_of_nonneg_left hy (abs_nonneg _))) le_rfl
        _ = _ := by ring
    have HB : |g r| + |c r 0| * Q + (|c r 1| + |c r 2|) * R ≤
        |g r| + C * A * (|c r 1| + |c r 2|) + coupledVariationFeedback C (l r) (c r) * Q := by
      dsimp [R, coupledVariationFeedback]
      nlinarith only [mul_nonneg (mul_nonneg hC (abs_nonneg (c r 0))) hQ,
        mul_nonneg (mul_nonneg (hl0 r hr) (add_nonneg (abs_nonneg (c r 1)) (abs_nonneg (c r 2)))) hQ]
    rw [abs_mul, abs_of_nonneg (hq r hr)]
    exact (mul_le_mul_of_nonneg_left (HT.trans HB) (hq r hr)).trans_eq (by dsimp [e, K]; ring)
  have H := abs_bounds_of_forced_derivative_feedback hst hZ hK hK0 he he0 hbudget (by linarith) hfeedback
  have hB : 0 ≤ B := (intervalIntegral.integral_nonneg hst he0).trans hsource
  have hM : (|Z s| + ∫ r in s..t, e r) / (1 - Λ) ≤ 2 * B := by
    rw [hZs, abs_zero, zero_add]
    apply (div_le_iff₀ (by linarith : 0 < 1 - Λ)).mpr
    have HΛ := mul_le_mul_of_nonneg_right hΛ hB
    nlinarith only [hsource, HΛ]
  have hz (r : ℝ) (hr : r ∈ Icc s t) : |Z r| ≤ 2 * B := (H r hr).1.trans hM
  intro r hr
  exact ⟨hz r hr, (hcap (2 * B) hz r hr).trans_eq (by ring)⟩

end BianchiIX
