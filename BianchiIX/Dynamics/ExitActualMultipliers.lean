import BianchiIX.Dynamics.ExitClockWallFactor

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

/-- Actual wall multipliers and their ordinary logarithmic derivatives, uniformly along the terminal flight. -/
theorem exists_terminal_exitClock_multiplier_bounds {η : ℝ} (hη : 0 < η ∧ η < 1) {J : ℕ} (hJ : 1 ≤ J) :
    ∃ C ≥ (1 : ℝ), ∃ ε > (0 : ℝ), ∀ α b u w : ℝ,
      (0 < α ∧ α ≤ 1) → 0 < b → b ≤ ε * α ^ J → |u| + |w| ≤ b →
      let Y : ExitTailState := ![2 + 2 * α, u, w]
      let h := η * α ^ J
      let S := exitTailLength η α J
      coreTailValid h Y ∧ ∃ I : Set ℝ, IsOpen I ∧ Convex ℝ I ∧ Icc 0 (coreTailTime h Y) ⊆ I ∧
        ∃ U : Set ExitTailState, IsOpen U ∧ Y ∈ U ∧ (∀ Z ∈ U, ∀ t ∈ I, exitEntryRegular Z t) ∧
        exitClockFlow I (Y, 0) = Y ∧
        ((fun Z => toExitTailState (coreTailState h Z)) =ᶠ[𝓝 Y] (fun Z => exitClockFlow I (Z, S))) ∧
        ∀ s ∈ Icc 0 S, ContDiffAt ℝ 2 (exitClockFlow I) (Y, s) ∧
          ‖fderiv ℝ (fun Z => exitClockFlow I (Z, s)) Y‖ ≤ C ∧
          (∀ i : Fin 2,
            exitClockFlow I (Y, s) i.succ = Y i.succ * Real.exp (exitClockLogMultiplier I i Y s) ∧
            ContDiffAt ℝ 1 (fun Z => exitClockLogMultiplier I i Z s) Y ∧
            1 / C ≤ Real.exp (exitClockLogMultiplier I i Y s) ∧
            Real.exp (exitClockLogMultiplier I i Y s) ≤ C ∧
            ∀ v : ExitTailState,
              fderiv ℝ (fun Z => exitClockFlow I (Z, s)) Y v i.succ =
                Real.exp (exitClockLogMultiplier I i Y s) * v i.succ +
                exitClockFlow I (Y, s) i.succ * fderiv ℝ (fun Z => exitClockLogMultiplier I i Z s) Y v) ∧
          ‖fderiv ℝ (fun Z => exitClockLogMultiplier I 0 Z s) Y‖ +
            ‖fderiv ℝ (fun Z => exitClockLogMultiplier I 1 Z s) Y‖ ≤ C * s := by
  obtain ⟨εe, hεe, HE⟩ := exists_terminal_exitClock_family hη hJ
  obtain ⟨A, hA, ε₀, hε₀, H₀⟩ := exists_exitTail_scale_bounds ⟨hη.1, hη.2.le⟩ hJ
  obtain ⟨K, hK, ε₁, hε₁, H₁⟩ := exists_exitTail_uniform_linear_bound ⟨hη.1, hη.2.le⟩ hJ
  let C := A + 3072 * K
  have hC : 1 ≤ C := by dsimp only [C]; linarith only [hA, hK]
  have hC0 : 0 < C := lt_of_lt_of_le (by norm_num) hC
  have hAC : A ≤ C := by dsimp only [C]; linarith only [hK]
  have hKC : K ≤ C := by dsimp only [C]; linarith only [hA, hK]
  have hDC : 3072 * K ≤ C := by dsimp only [C]; linarith only [hA]
  have hA0 : 0 < A := by linarith only [hA]
  let ε := min εe (min ε₀ ε₁)
  refine ⟨C, hC, ε, lt_min hεe (lt_min hε₀ hε₁), ?_⟩
  intro α b u w hα hb hsmall hw Y h S
  have he := hsmall.trans (mul_le_mul_of_nonneg_right (min_le_left εe (min ε₀ ε₁)) (pow_nonneg hα.1.le J))
  have hb₀ := hsmall.trans (mul_le_mul_of_nonneg_right
    ((min_le_right εe (min ε₀ ε₁)).trans (min_le_left ε₀ ε₁)) (pow_nonneg hα.1.le J))
  have hb₁ := hsmall.trans (mul_le_mul_of_nonneg_right
    ((min_le_right εe (min ε₀ ε₁)).trans (min_le_right ε₀ ε₁)) (pow_nonneg hα.1.le J))
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
  have HP := H₀ α b S β hα hb hb₀ ⟨hS, le_rfl⟩ hR hwall hβ
  have hnorm (s : ℝ) (hs : s ∈ Icc 0 S) : ‖fderiv ℝ (fun Z => exitClockFlow I (Z, s)) Y‖ ≤ K := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by linarith only [hK])
    intro v
    rw [fderiv_parameterSlice_apply ((HF s hs).1.differentiableAt (by norm_num)) v]
    have HB := H₁ α b S β hα hb hb₁ ⟨hS, le_rfl⟩ hR hwall hβ
      (fun r => fderiv ℝ (exitClockFlow I) (Y, r) (v, 0)) 0 s le_rfl hs.1 hs.2
      (fun r hr => (HF r ⟨hr.1, hr.2.trans hs.2⟩).2.2 v)
    rwa [exitClockFlow_variation_initial hIo hI hUo hYU HR (hcover ⟨le_rfl, hT⟩) v] at HB
  refine ⟨hvalid, I, hIo, hI, hcover, U, hUo, hYU, HR, hinit, hend, ?_⟩
  intro s hs
  have hsub : Icc 0 s ⊆ Icc 0 S := fun _ hr => ⟨hr.1, hr.2.trans hs.2⟩
  have HL (i : Fin 2) := exitClockLogMultiplier_derivative_bound hs.1 (by linarith only [hK] : 0 ≤ K)
    (fun r hr => (HF r (hsub hr)).1.of_le (by norm_num))
    (fun r hr => ⟨(HP r (hsub hr)).1.1, (HP r (hsub hr)).1.2.1, (HP r (hsub hr)).1.2.2.1⟩)
    (fun r hr => hnorm r (hsub hr)) i
  refine ⟨(HF s hs).1, (hnorm s hs).trans hKC, ?_, ?_⟩
  · intro i
    have HM := (HP s hs).2.1 i
    have heq : Real.exp (exitClockLogMultiplier I i Y s) = exitTailMultiplier β i s := rfl
    have Hval : exitClockFlow I (Y, s) i.succ = Y i.succ * Real.exp (exitClockLogMultiplier I i Y s) := by
      rw [heq]
      simpa only [hβ0] using HM.1
    refine ⟨Hval, (HL i).1, ?_, ?_, ?_⟩
    · rw [heq]
      apply le_trans _ HM.2.1
      apply (div_le_div_iff₀ hC0 hA0).mpr
      nlinarith only [hAC, hC0]
    · rw [heq]
      exact HM.2.2.trans (by linarith only [hAC, hA0])
    · exact exitClockFlow_wall_differential hIo hI hUo hYU HR hT hcover (hclock ▸ hs) i
  · nlinarith only [(HL 0).2, (HL 1).2, mul_le_mul_of_nonneg_right hDC hs.1]

end BianchiIX
