import BianchiIX.Analysis.CoreIntegrals

noncomputable section

namespace BianchiIX

open Set MeasureTheory

/-- A subunit total feedback budget is absorbed at a maximum on the compact interval. -/
theorem abs_bounds_of_forced_derivative_feedback {f f' k e : ℝ → ℝ} {a b Λ : ℝ}
    (hab : a ≤ b) (hf : ∀ t ∈ Icc a b, HasDerivAt f (f' t) t)
    (hk : ContinuousOn k (Icc a b)) (hk0 : ∀ t ∈ Icc a b, 0 ≤ k t)
    (he : ContinuousOn e (Icc a b)) (he0 : ∀ t ∈ Icc a b, 0 ≤ e t)
    (hbudget : (∫ t in a..b, k t) ≤ Λ) (hΛ : Λ < 1)
    (hfeedback : ∀ Q : ℝ, 0 ≤ Q → (∀ t ∈ Icc a b, |f t| ≤ Q) →
      ∀ t ∈ Icc a b, |f' t| ≤ e t + k t * Q) :
    ∀ t ∈ Icc a b, |f t| ≤ (|f a| + ∫ s in a..b, e s) / (1 - Λ) ∧
      |f t - f a| ≤ (∫ s in a..b, e s) + Λ * (|f a| + ∫ s in a..b, e s) / (1 - Λ) := by
  obtain ⟨r, hr, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hab)
    (HasDerivAt.continuousOn hf).abs
  have hbound (t : ℝ) (ht : t ∈ Icc a b) : |f t| ≤ |f r| := hmax ht
  have hd := hfeedback |f r| (abs_nonneg _) hbound
  have hΛ0 : 0 ≤ Λ := (intervalIntegral.integral_nonneg hab hk0).trans hbudget
  have hkmeas : 0 ≤ᵐ[volume.restrict (Ioc a b)] k :=
    ae_restrict_of_forall_mem measurableSet_Ioc (fun t ht => hk0 t ⟨ht.1.le, ht.2⟩)
  have hemeas : 0 ≤ᵐ[volume.restrict (Ioc a b)] e :=
    ae_restrict_of_forall_mem measurableSet_Ioc (fun t ht => he0 t ⟨ht.1.le, ht.2⟩)
  have hinc (t : ℝ) (ht : t ∈ Icc a b) : |f t - f a| ≤ (∫ s in a..b, e s) + Λ * |f r| := by
    have hsub : Icc a t ⊆ Icc a b := Icc_subset_Icc_right ht.2
    have hmajor : ContinuousOn (fun z => e z + k z * |f r|) (Icc a t) :=
      (he.mono hsub).add ((hk.mono hsub).mul_const |f r|)
    have H := abs_sub_le_integral_bound ht.1 (fun z hz => hf z (hsub hz))
      hmajor (fun z hz => hd z (hsub hz))
    rw [intervalIntegral.integral_add ((he.mono hsub).intervalIntegrable_of_Icc ht.1)
      (((hk.mono hsub).mul_const |f r|).intervalIntegrable_of_Icc ht.1),
      intervalIntegral.integral_mul_const] at H
    have HI := (intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2 hkmeas
      (hk.intervalIntegrable_of_Icc hab)).trans hbudget
    have HE := intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2 hemeas
      (he.intervalIntegrable_of_Icc hab)
    exact H.trans (add_le_add HE (mul_le_mul_of_nonneg_right HI (abs_nonneg _)))
  have hM : |f r| ≤ (|f a| + ∫ s in a..b, e s) / (1 - Λ) := by
    apply (le_div_iff₀ (sub_pos.mpr hΛ)).mpr
    have H : |f r| ≤ |f r - f a| + |f a| := by
      simpa using abs_add_le (f r - f a) (f a)
    nlinarith only [H, hinc r hr]
  intro t ht
  refine ⟨(hbound t ht).trans hM, ?_⟩
  calc
    _ ≤ (∫ s in a..b, e s) + Λ * |f r| := hinc t ht
    _ ≤ (∫ s in a..b, e s) + Λ * ((|f a| + ∫ s in a..b, e s) / (1 - Λ)) :=
      add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hM hΛ0)
    _ = _ := by ring

theorem abs_bounds_of_derivative_feedback {f f' k : ℝ → ℝ} {a b Λ : ℝ}
    (hab : a ≤ b) (hf : ∀ t ∈ Icc a b, HasDerivAt f (f' t) t)
    (hk : ContinuousOn k (Icc a b)) (hk0 : ∀ t ∈ Icc a b, 0 ≤ k t)
    (hbudget : (∫ t in a..b, k t) ≤ Λ) (hΛ : Λ < 1)
    (hfeedback : ∀ Q : ℝ, 0 ≤ Q → (∀ t ∈ Icc a b, |f t| ≤ Q) →
      ∀ t ∈ Icc a b, |f' t| ≤ k t * Q) :
    ∀ t ∈ Icc a b, |f t| ≤ |f a| / (1 - Λ) ∧
      |f t - f a| ≤ Λ * |f a| / (1 - Λ) := by
  have H := abs_bounds_of_forced_derivative_feedback (e := fun _ => 0) hab hf hk hk0
    continuousOn_const (fun _ _ => le_rfl) hbudget hΛ
    (fun Q hQ hbound t ht => by simpa only [zero_add] using hfeedback Q hQ hbound t ht)
  simpa only [intervalIntegral.integral_zero, add_zero, zero_add] using H

end BianchiIX
