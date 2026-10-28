import BianchiIX.Dynamics.ExitTailScale

noncomputable section

namespace BianchiIX

open Set

theorem exitTail_refined_radial_bound {Y : ℝ → ExitTailState} {T α b A D : ℝ}
    (hT : 0 ≤ T) (hb : 0 ≤ b) (hA : 0 ≤ A)
    (hY : ∀ s ∈ Icc 0 T, HasDerivAt Y (exitTailField (Real.exp (-s)) (Y s)) s)
    (hreg : ∀ s ∈ Icc 0 T, exitTailRegion α b A D (Y s))
    (hU : ∀ s ∈ Icc 0 T, |Y s 1| ≤ A * |Y 0 1|) :
    |Y T 0 - Y 0 0| ≤ 20 * (A * |Y 0 1| + (A * b) ^ 2 * T) := by
  have H := abs_sub_le_integral_bound hT
    (fun s hs => hasDerivAt_pi.mp (hY s hs) 0)
    (B := fun s => 20 * (A * b) ^ 2 + (20 * A * |Y 0 1|) * Real.exp (-s) + 0 * Real.exp (-2 * s))
    (by fun_prop) ?_
  · have HI := integral_exit_tail_envelope (T := T) (A := 20 * (A * b) ^ 2)
      (by positivity : 0 ≤ 20 * A * |Y 0 1|) (by norm_num : (0 : ℝ) ≤ 0)
    exact H.trans (HI.trans_eq (by ring))
  · intro s hs
    obtain ⟨hR, hu, hw, hsum, _⟩ := hreg s hs
    have hv : 0 ≤ Real.exp (-s) ∧ Real.exp (-s) ≤ 1 :=
      ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr (neg_nonpos.mpr hs.1)⟩
    have Hp := (exitTail_perturbation_bounds hR hu hv hw).1
    have hsq := (sq_le_sq₀ (add_nonneg (abs_nonneg _) (abs_nonneg _)) (mul_nonneg hA hb)).mpr hsum
    have hm := mul_le_mul_of_nonneg_right (hU s hs) hv.1
    change |exitTailRadial (Y s 0) (Y s 1) (Real.exp (-s)) (Y s 2)| ≤ _
    nlinarith only [Hp, hsq, hm]

theorem exists_exitTail_refined_scale_bounds {η : ℝ} (hη : 0 < η ∧ η ≤ 1) {J : ℕ} (hJ : 1 ≤ J) :
    ∃ C ≥ (1 : ℝ), ∃ ε > (0 : ℝ), ∀ α b T : ℝ, ∀ Y : ℝ → ExitTailState,
      (0 < α ∧ α ≤ 1) → 0 < b → b ≤ ε * α ^ J → (0 ≤ T ∧ T ≤ exitTailLength η α J) →
      Y 0 0 = 2 + 2 * α → |Y 0 1| + |Y 0 2| ≤ b →
      (∀ s ∈ Icc 0 T, HasDerivAt Y (exitTailField (Real.exp (-s)) (Y s)) s) →
      ∀ s ∈ Icc 0 T, |Y s 0 - Y 0 0| ≤ C * (|Y 0 1| + b ^ 2 * s) ∧
        ((0 ≤ Y 0 1 ∧ 0 ≤ Y 0 2) → Y s 2 ≤ Y 0 2 * Real.exp (α / (1 + α) * s)) := by
  obtain ⟨A, hA, ε₁, hε₁, H₁⟩ := exists_exitTail_scale_bounds hη hJ
  obtain ⟨B, _, ε₂, hε₂, H₂⟩ := exists_exitTail_positive_scale_bounds hη hJ
  have hA0 : 0 < A := by linarith only [hA]
  have hAA : A ≤ A ^ 2 := by nlinarith only [hA]
  refine ⟨20 * A ^ 2, by nlinarith only [hA, hAA], min ε₁ ε₂, lt_min hε₁ hε₂, ?_⟩
  intro α b T Y hα hb hsmall hT hR hw hY
  have hb₁ := hsmall.trans (mul_le_mul_of_nonneg_right (min_le_left ε₁ ε₂) (pow_nonneg hα.1.le J))
  have hb₂ := hsmall.trans (mul_le_mul_of_nonneg_right (min_le_right ε₁ ε₂) (pow_nonneg hα.1.le J))
  have HP := H₁ α b T Y hα hb hb₁ hT hR hw hY
  have hU (s : ℝ) (hs : s ∈ Icc 0 T) : |Y s 1| ≤ A * |Y 0 1| := by
    obtain ⟨HM, _, HMbound⟩ := (HP s hs).2.1 0
    change Y s 1 = Y 0 1 * exitTailMultiplier Y 0 s at HM
    have hMpos : 0 < exitTailMultiplier Y 0 s := Real.exp_pos _
    rw [HM, abs_mul, abs_of_pos hMpos]
    nlinarith only [mul_le_mul_of_nonneg_left HMbound (abs_nonneg (Y 0 1)),
      mul_nonneg hA0.le (abs_nonneg (Y 0 1))]
  intro s hs
  have hsub : Icc 0 s ⊆ Icc 0 T := fun _ hr => ⟨hr.1, hr.2.trans hs.2⟩
  have HR := exitTail_refined_radial_bound hs.1 hb.le hA0.le
    (fun r hr => hY r (hsub hr)) (fun r hr => (HP r (hsub hr)).1) (fun r hr => hU r (hsub hr))
  refine ⟨HR.trans ?_, ?_⟩
  · nlinarith only [mul_le_mul_of_nonneg_right hAA (abs_nonneg (Y 0 1))]
  · intro hpos
    have hsum : Y 0 1 + Y 0 2 ≤ b := by
      simpa only [abs_of_nonneg hpos.1, abs_of_nonneg hpos.2] using hw
    exact ((H₂ α b T Y hα hb hb₂ hT hR hpos hsum hY).2 s hs).2.2.1.2

end BianchiIX
