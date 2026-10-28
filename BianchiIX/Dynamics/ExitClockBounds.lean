import BianchiIX.Dynamics.ExitActualClock
import BianchiIX.Dynamics.ExitClockSecondVariation

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

/-- The actual terminal clock flow satisfies the full ordinary-coordinate bounds of D.3. -/
theorem exists_terminal_exitClock_two_bounds {η : ℝ} (hη : 0 < η ∧ η < 1) {J : ℕ} (hJ : 1 ≤ J) :
    ∃ C ≥ (1 : ℝ), ∃ ε > (0 : ℝ), ∀ α b u w : ℝ,
      (0 < α ∧ α ≤ 1) → 0 < b → b ≤ ε * α ^ J → |u| + |w| ≤ b →
      let Y : ExitTailState := ![2 + 2 * α, u, w]
      let h := η * α ^ J
      let S := exitTailLength η α J
      coreTailValid h Y ∧ ∃ I : Set ℝ, IsOpen I ∧ Convex ℝ I ∧ Icc 0 (coreTailTime h Y) ⊆ I ∧
        (∀ t ∈ I, exitEntryRegular Y t) ∧ exitClockFlow I (Y, 0) = Y ∧
        ((fun Z => toExitTailState (coreTailState h Z)) =ᶠ[𝓝 Y] (fun Z => exitClockFlow I (Z, S))) ∧
        ∀ s ∈ Icc 0 S,
          ContDiffAt ℝ 2 (fun Z => exitClockFlow I (Z, s)) Y ∧
          HasDerivAt (fun r => exitClockFlow I (Y, r))
            (exitTailField (Real.exp (-s)) (exitClockFlow I (Y, s))) s ∧
          |exitClockFlow I (Y, s) 0 - Y 0| + |exitClockFlow I (Y, s) 1| +
            |exitClockFlow I (Y, s) 2| ≤ C * b ∧
          ‖fderiv ℝ (fun Z => exitClockFlow I (Z, s)) Y‖ ≤ C ∧
          ‖fderiv ℝ (fderiv ℝ (fun Z => exitClockFlow I (Z, s))) Y‖ ≤ C * s := by
  obtain ⟨εe, hεe, HE⟩ := exists_terminal_exitClock_family hη hJ
  obtain ⟨A, hA, ε₀, hε₀, H₀⟩ := exists_exitTail_scale_bounds ⟨hη.1, hη.2.le⟩ hJ
  obtain ⟨C₁, hC₁, ε₁, hε₁, H₁⟩ := exists_exitTail_uniform_linear_bound ⟨hη.1, hη.2.le⟩ hJ
  obtain ⟨C₂, hC₂, ε₂, hε₂, H₂⟩ := exists_exitTail_uniform_second_bound ⟨hη.1, hη.2.le⟩ hJ
  let C := 41 * A + C₁ + C₂
  have hC : 1 ≤ C := by dsimp only [C]; linarith only [hA, hC₁, hC₂]
  have hC0 : 0 ≤ C := le_trans (by norm_num) hC
  have hA' : 41 * A ≤ C := by dsimp only [C]; linarith only [hC₁, hC₂]
  have hC₁' : C₁ ≤ C := by dsimp only [C]; linarith only [hA, hC₂]
  have hC₂' : C₂ ≤ C := by dsimp only [C]; linarith only [hA, hC₁]
  let ε := min εe (min ε₀ (min ε₁ ε₂))
  refine ⟨C, hC, ε, lt_min hεe (lt_min hε₀ (lt_min hε₁ hε₂)), ?_⟩
  intro α b u w hα hb hsmall hw Y h S
  have he : b ≤ εe * α ^ J := hsmall.trans
    (mul_le_mul_of_nonneg_right (min_le_left _ _) (pow_nonneg hα.1.le J))
  have hsmall₀ : b ≤ ε₀ * α ^ J := hsmall.trans
    (mul_le_mul_of_nonneg_right ((min_le_right _ _).trans (min_le_left _ _)) (pow_nonneg hα.1.le J))
  have hsmall₁ : b ≤ ε₁ * α ^ J := hsmall.trans
    (mul_le_mul_of_nonneg_right ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
      (pow_nonneg hα.1.le J))
  have hsmall₂ : b ≤ ε₂ * α ^ J := hsmall.trans
    (mul_le_mul_of_nonneg_right ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
      (pow_nonneg hα.1.le J))
  obtain ⟨hvalid, I, hIo, hI, hcover, U, hUo, hYU, HR, hinit, hend, HF⟩ := HE α b u w hα hb he hw
  change coreTailValid h Y at hvalid
  have hT : 0 ≤ coreTailTime h Y := hvalid.1.1.1.le
  have hS : 0 ≤ S := exitTailLength_nonneg ⟨hη.1, hη.2.le⟩ hα J
  have hclock : exitEntryClock (Y, coreTailTime h Y) = S := by
    change -Real.log (coreTailState h Y 2) = S
    rw [coreTailState_active hvalid]
    change -Real.log (η * α ^ J) = exitTailLength η α J
    rw [← exp_neg_exitTailLength hη.1 hα.1 J, Real.log_exp, neg_neg]
  let β : ℝ → ExitTailState := fun s => exitClockFlow I (Y, s)
  have hβ0 : β 0 = Y := hinit
  have hR : β 0 0 = 2 + 2 * α := by rw [hβ0]; rfl
  have hwall : |β 0 1| + |β 0 2| ≤ b := by rw [hβ0]; exact hw
  have hβ (s : ℝ) (hs : s ∈ Icc 0 S) : HasDerivAt β (exitTailField (Real.exp (-s)) (β s)) s :=
    (HF s hs).2.1
  have hvar0 (v : ExitTailState) : fderiv ℝ (exitClockFlow I) (Y, 0) (v, 0) = v :=
    exitClockFlow_variation_initial hIo hI hUo hYU HR (hcover ⟨le_rfl, hT⟩) v
  have hval := H₀ α b S β hα hb hsmall₀ ⟨hS, le_rfl⟩ hR hwall hβ
  refine ⟨hvalid, I, hIo, hI, hcover, HR Y hYU, hinit, hend, ?_⟩
  intro s hs
  have hΦ := (HF s hs).1
  have hslice : ContDiffAt ℝ 2 (fun Z => exitClockFlow I (Z, s)) Y := by
    have HS := hΦ.comp Y (contDiffAt_id.prodMk (contDiffAt_const (c := s)))
    exact HS
  have hsub : Icc 0 s ⊆ Icc 0 S := fun _ ht => ⟨ht.1, ht.2.trans hs.2⟩
  refine ⟨hslice, hβ s hs, ?_, ?_, ?_⟩
  · have HV := (hval s hs).2.2.1
    have HD := (hval s hs).2.2.2.1
    rw [hβ0] at HD
    have HAb := mul_le_mul_of_nonneg_right hA' hb.le
    change |β s 0 - Y 0| + |β s 1| + |β s 2| ≤ C * b
    nlinarith only [HD, HV, HAb, mul_nonneg (by linarith only [hA] : 0 ≤ A) hb.le]
  · apply ContinuousLinearMap.opNorm_le_bound _ hC0
    intro v
    rw [fderiv_parameterSlice_apply (hΦ.differentiableAt (by norm_num)) v]
    have HB := H₁ α b S β hα hb hsmall₁ ⟨hS, le_rfl⟩ hR hwall hβ
      (fun r => fderiv ℝ (exitClockFlow I) (Y, r) (v, 0)) 0 s le_rfl hs.1 hs.2
      (fun r hr => (HF r (hsub hr)).2.2 v)
    rw [hvar0] at HB
    exact HB.trans (mul_le_mul_of_nonneg_right hC₁' (norm_nonneg v))
  · apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hC0 hs.1)
    intro v
    apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (mul_nonneg hC0 hs.1) (norm_nonneg v))
    intro w
    obtain ⟨Q, hQ0, HQ⟩ := exists_exitClockFlow_second_variation hIo hI hUo hYU HR hT hcover v w
    rw [hclock] at HQ
    rw [← (HQ s hs).1]
    have HB := H₂ α b s β
      (fun r => fderiv ℝ (exitClockFlow I) (Y, r) (v, 0))
      (fun r => fderiv ℝ (exitClockFlow I) (Y, r) (w, 0)) Q
      hα hb hsmall₂ hs hR hwall (fun r hr => hβ r (hsub hr))
      (fun r hr => (HF r (hsub hr)).2.2 v) (fun r hr => (HF r (hsub hr)).2.2 w)
      (fun r hr => (HQ r (hsub hr)).2) hQ0
    rw [hvar0, hvar0] at HB
    exact HB.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hC₂' hs.1) (norm_nonneg v)) (norm_nonneg w))

theorem exists_terminal_exitReturn_two_bounds {η : ℝ} (hη : 0 < η ∧ η < 1) {J : ℕ} (hJ : 1 ≤ J) :
    ∃ C ≥ (1 : ℝ), ∃ ε > (0 : ℝ), ∀ α b u w : ℝ,
      (0 < α ∧ α ≤ 1) → 0 < b → b ≤ ε * α ^ J → |u| + |w| ≤ b →
      let Y : ExitTailState := ![2 + 2 * α, u, w]
      let h := η * α ^ J
      coreTailValid h Y ∧ ContDiffAt ℝ 2 (fun Z => toExitTailState (coreTailState h Z)) Y ∧
        ‖fderiv ℝ (fun Z => toExitTailState (coreTailState h Z)) Y‖ ≤ C ∧
        ‖fderiv ℝ (fderiv ℝ (fun Z => toExitTailState (coreTailState h Z))) Y‖ ≤
          C * exitTailLength η α J := by
  obtain ⟨C, hC, ε, hε, HE⟩ := exists_terminal_exitClock_two_bounds hη hJ
  refine ⟨C, hC, ε, hε, ?_⟩
  intro α b u w hα hb hsmall hw Y h
  obtain ⟨hvalid, I, _, _, _, _, _, hend, HF⟩ := HE α b u w hα hb hsmall hw
  have hS := exitTailLength_nonneg ⟨hη.1, hη.2.le⟩ hα J
  have HS := HF _ ⟨hS, le_rfl⟩
  refine ⟨hvalid, HS.1.congr_of_eventuallyEq hend, ?_, ?_⟩
  · rw [hend.fderiv_eq]
    exact HS.2.2.2.1
  · rw [hend.fderiv.fderiv_eq]
    exact HS.2.2.2.2

end BianchiIX
