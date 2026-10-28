import BianchiIX.Dynamics.CoreTailHeightOrder
import BianchiIX.Dynamics.ExitClockBounds

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

/-- The ordinary first and second tail derivatives are uniform over an entire height interval. -/
theorem exists_terminal_exitReturn_two_bounds_uniform {η₀ : ℝ} (hη₀ : 0 < η₀ ∧ η₀ < 1)
    {J : ℕ} (hJ : 1 ≤ J) :
    ∃ C ≥ (1 : ℝ), ∃ ε > (0 : ℝ), ∀ η α b u w : ℝ,
      η₀ ≤ η → η < 1 → (0 < α ∧ α ≤ 1) → 0 < b →
      b ≤ ε * α ^ J → |u| + |w| ≤ b →
      let Y : ExitTailState := ![2 + 2 * α, u, w]
      let h := η * α ^ J
      coreTailValid h Y ∧ ContDiffAt ℝ 2 (fun Z => toExitTailState (coreTailState h Z)) Y ∧
        ‖fderiv ℝ (fun Z => toExitTailState (coreTailState h Z)) Y‖ ≤ C ∧
        ‖fderiv ℝ (fderiv ℝ (fun Z => toExitTailState (coreTailState h Z))) Y‖ ≤
          C * exitTailLength η α J := by
  obtain ⟨εe, hεe, HE⟩ := exists_terminal_exitClock_family hη₀ hJ
  obtain ⟨C₁, hC₁, ε₁, hε₁, H₁⟩ := exists_exitTail_uniform_linear_bound ⟨hη₀.1, hη₀.2.le⟩ hJ
  obtain ⟨C₂, hC₂, ε₂, hε₂, H₂⟩ := exists_exitTail_uniform_second_bound ⟨hη₀.1, hη₀.2.le⟩ hJ
  let C := C₁ + C₂
  have hC : 1 ≤ C := by dsimp only [C]; linarith only [hC₁, hC₂]
  have hC0 : 0 ≤ C := le_trans (by norm_num) hC
  have hC₁' : C₁ ≤ C := by dsimp only [C]; linarith only [hC₂]
  have hC₂' : C₂ ≤ C := by dsimp only [C]; linarith only [hC₁]
  let ε := min εe (min ε₁ ε₂)
  refine ⟨C, hC, ε, lt_min hεe (lt_min hε₁ hε₂), ?_⟩
  intro η α b u w hηlo hηhi hα hb hsmall hw Y h
  have hη : 0 < η := hη₀.1.trans_le hηlo
  have he : b ≤ εe * α ^ J := hsmall.trans
    (mul_le_mul_of_nonneg_right (min_le_left _ _) (pow_nonneg hα.1.le J))
  have hsmall₁ : b ≤ ε₁ * α ^ J := hsmall.trans
    (mul_le_mul_of_nonneg_right ((min_le_right _ _).trans (min_le_left _ _)) (pow_nonneg hα.1.le J))
  have hsmall₂ : b ≤ ε₂ * α ^ J := hsmall.trans
    (mul_le_mul_of_nonneg_right ((min_le_right _ _).trans (min_le_right _ _)) (pow_nonneg hα.1.le J))
  obtain ⟨HV₀, I, hIo, hI, hcover, U, hUo, hYU, HR, hinit, _, HF⟩ := HE α b u w hα hb he hw
  have hh1 : h < 1 := by
    have H := mul_le_mul_of_nonneg_left (pow_le_one₀ hα.1.le hα.2 (n := J)) hη.le
    exact H.trans_lt (by simpa only [mul_one] using hηhi)
  obtain ⟨HV, htime⟩ := coreTailValid_of_height_le HV₀
    (mul_le_mul_of_nonneg_right hηlo (pow_nonneg hα.1.le J)) hh1
  let S := exitTailLength η α J
  let S₀ := exitTailLength η₀ α J
  have hS : 0 ≤ S := exitTailLength_nonneg ⟨hη, hηhi.le⟩ hα J
  have hS₀ : 0 ≤ S₀ := exitTailLength_nonneg ⟨hη₀.1, hη₀.2.le⟩ hα J
  have hSS₀ : S ≤ S₀ := by
    have H := mul_le_mul_of_nonneg_right hηlo (pow_nonneg hα.1.le J)
    rw [← exp_neg_exitTailLength hη₀.1 hα.1 J, ← exp_neg_exitTailLength hη hα.1 J] at H
    exact neg_le_neg_iff.mp (Real.exp_le_exp.mp H)
  have hs : S ∈ Icc 0 S₀ := ⟨hS, hSS₀⟩
  have hsub : Icc 0 S ⊆ Icc 0 S₀ := fun _ ht => ⟨ht.1, ht.2.trans hSS₀⟩
  have hT : 0 ≤ coreTailTime (η₀ * α ^ J) Y := HV₀.1.1.1.le
  have hclock : exitEntryClock (Y, coreTailTime (η₀ * α ^ J) Y) = S₀ := by
    change -Real.log (coreTailState (η₀ * α ^ J) Y 2) = S₀
    rw [coreTailState_active HV₀, ← exp_neg_exitTailLength hη₀.1 hα.1 J, Real.log_exp, neg_neg]
  have heh : -Real.log h = S := by
    change -Real.log (η * α ^ J) = S
    rw [← exp_neg_exitTailLength hη hα.1 J, Real.log_exp, neg_neg]
  have hend := coreTailState_eventuallyEq_exitClockFlow hIo hI hUo hYU HR HV
    (hcover ⟨HV.1.1.1.le, htime⟩)
  rw [heh] at hend
  let β : ℝ → ExitTailState := fun s => exitClockFlow I (Y, s)
  have hβ0 : β 0 = Y := hinit
  have hR : β 0 0 = 2 + 2 * α := by rw [hβ0]; rfl
  have hwall : |β 0 1| + |β 0 2| ≤ b := by rw [hβ0]; exact hw
  have hβ (s : ℝ) (hs : s ∈ Icc 0 S₀) : HasDerivAt β (exitTailField (Real.exp (-s)) (β s)) s :=
    (HF s hs).2.1
  have hvar0 (v : ExitTailState) : fderiv ℝ (exitClockFlow I) (Y, 0) (v, 0) = v :=
    exitClockFlow_variation_initial hIo hI hUo hYU HR (hcover ⟨le_rfl, hT⟩) v
  have hΦ := (HF S hs).1
  have hslice : ContDiffAt ℝ 2 (fun Z => exitClockFlow I (Z, S)) Y :=
    ContDiffAt.comp (g := exitClockFlow I) (f := fun Z : ExitTailState => (Z, S)) Y
      hΦ (contDiffAt_id.prodMk (contDiffAt_const (c := S)))
  refine ⟨HV, hslice.congr_of_eventuallyEq hend, ?_, ?_⟩
  · rw [hend.fderiv_eq]
    apply ContinuousLinearMap.opNorm_le_bound _ hC0
    intro v
    rw [fderiv_parameterSlice_apply (hΦ.differentiableAt (by norm_num)) v]
    have HB := H₁ α b S₀ β hα hb hsmall₁ ⟨hS₀, le_rfl⟩ hR hwall hβ
      (fun r => fderiv ℝ (exitClockFlow I) (Y, r) (v, 0)) 0 S le_rfl hS hSS₀
      (fun r hr => (HF r (hsub hr)).2.2 v)
    rw [hvar0] at HB
    exact HB.trans (mul_le_mul_of_nonneg_right hC₁' (norm_nonneg v))
  · rw [hend.fderiv.fderiv_eq]
    apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hC0 hS)
    intro v
    apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (mul_nonneg hC0 hS) (norm_nonneg v))
    intro w
    obtain ⟨Q, hQ0, HQ⟩ := exists_exitClockFlow_second_variation hIo hI hUo hYU HR hT hcover v w
    rw [hclock] at HQ
    rw [← (HQ S hs).1]
    have HB := H₂ α b S β
      (fun r => fderiv ℝ (exitClockFlow I) (Y, r) (v, 0))
      (fun r => fderiv ℝ (exitClockFlow I) (Y, r) (w, 0)) Q
      hα hb hsmall₂ hs hR hwall (fun r hr => hβ r (hsub hr))
      (fun r hr => (HF r (hsub hr)).2.2 v) (fun r hr => (HF r (hsub hr)).2.2 w)
      (fun r hr => (HQ r (hsub hr)).2) hQ0
    rw [hvar0, hvar0] at HB
    exact HB.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hC₂' hS) (norm_nonneg v)) (norm_nonneg w))

end BianchiIX
