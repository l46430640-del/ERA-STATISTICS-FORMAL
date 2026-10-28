import BianchiIX.Dynamics.ExitActualRadialColumns
import BianchiIX.Dynamics.ExitClockWeakLogarithm

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

/-- All four estimates of D.10 hold for ordinary derivatives of the actual terminal flow. -/
theorem exists_terminal_exitClock_fine_columns {η : ℝ} (hη : 0 < η ∧ η < 1) {J : ℕ} (hJ : 1 ≤ J) :
    ∃ C ≥ (1 : ℝ), ∃ ε > (0 : ℝ), ∀ α b u w : ℝ,
      (0 < α ∧ α ≤ 1) → 0 < b → b ≤ ε * α ^ J → |u| + |w| ≤ b →
      let Y : ExitTailState := ![2 + 2 * α, u, w]
      let h := η * α ^ J
      let S := exitTailLength η α J
      coreTailValid h Y ∧ ∃ I : Set ℝ, IsOpen I ∧ Convex ℝ I ∧ Icc 0 (coreTailTime h Y) ⊆ I ∧
        (∀ t ∈ I, exitEntryRegular Y t) ∧ exitClockFlow I (Y, 0) = Y ∧
        ((fun Z => toExitTailState (coreTailState h Z)) =ᶠ[𝓝 Y] (fun Z => exitClockFlow I (Z, S))) ∧
        ∀ s ∈ Icc 0 S, ContDiffAt ℝ 2 (exitClockFlow I) (Y, s) ∧
          ‖fderiv ℝ (fun Z => exitClockFlow I (Z, s)) Y‖ ≤ C ∧
          |fderiv ℝ (fun Z => exitClockFlow I (Z, s)) Y (Pi.single 0 1) 0 - 1| ≤
            C * (|u| + b ^ 2 * (1 + s) ^ 2) ∧
          |fderiv ℝ (fun Z => exitClockFlow I (Z, s)) Y (Pi.single 2 1) 0| ≤ C * b * (1 + s) ∧
          ∀ i : Fin 2, ContDiffAt ℝ 1 (fun Z => exitClockLogMultiplier I i Z s) Y ∧
            |fderiv ℝ (fun Z => exitClockLogMultiplier I i Z s) Y (Pi.single 0 1)| ≤ C * s ∧
            |fderiv ℝ (fun Z => exitClockLogMultiplier I i Z s) Y (Pi.single 1 1)| ≤ C * s ∧
            |fderiv ℝ (fun Z => exitClockLogMultiplier I i Z s) Y (Pi.single 2 1)| ≤ C * (1 + b * s * (1 + s)) ∧
            |fderiv ℝ (fun Z => exitClockLogMultiplier I i Z s) Y (Pi.single 2 1)| ≤ C := by
  obtain ⟨A, hA, εr, hεr, HR⟩ := exists_terminal_exitClock_radial_columns hη hJ
  let Q := 2 * (1 + Real.log (1 / η)) ^ 2 + 8 * Real.exp (-2)
  have hQ : 0 < Q := by dsimp only [Q]; positivity
  let ε := min εr (1 / Q)
  let C := 4096 * A ^ 2
  have hA0 : 0 ≤ A := le_trans (by norm_num) hA
  have hAA : A ≤ A ^ 2 := by nlinarith only [hA]
  have hAC : A ≤ C := by dsimp only [C]; nlinarith only [hA, hAA]
  have hLC : 1536 * A ≤ C := by dsimp only [C]; nlinarith only [hA, hAA]
  have hWC : 1024 * A ^ 2 ≤ C := by dsimp only [C]; nlinarith only [sq_nonneg A]
  refine ⟨C, hA.trans hAC, ε, lt_min hεr (one_div_pos.mpr hQ), ?_⟩
  intro α b u w hα hb hsmall hw Y h S
  have hr := hsmall.trans (mul_le_mul_of_nonneg_right (min_le_left εr _) (pow_nonneg hα.1.le J))
  obtain ⟨hvalid, I, hIo, hI, hcover, Htube, hinit, hend, HF⟩ := HR α b u w hα hb hr hw
  have hbudget : b * (1 + S) ^ 2 ≤ 1 := by
    have HB := mul_le_mul_of_nonneg_right hsmall (sq_nonneg (1 + S))
    have HL := (exitTailLength_weighted_bounds ⟨hη.1, hη.2.le⟩ hα J).2.2
    have Hε : ε * Q ≤ 1 := (le_div_iff₀ hQ).mp (min_le_right εr _)
    have hε0 : 0 ≤ ε := (lt_min hεr (one_div_pos.mpr hQ)).le
    nlinarith only [HB, mul_le_mul_of_nonneg_left HL hε0, Hε]
  refine ⟨hvalid, I, hIo, hI, hcover, Htube, hinit, hend, ?_⟩
  intro s hs
  have hs0 : 0 ≤ s := hs.1
  have hsub : Icc 0 s ⊆ Icc 0 S := fun _ hr => ⟨hr.1, hr.2.trans hs.2⟩
  have hbs : b * s * (1 + s) ≤ 1 := by
    have H : s * (1 + s) ≤ (1 + S) ^ 2 := by nlinarith only [hs.1, hs.2, sq_nonneg (S - s)]
    nlinarith only [mul_le_mul_of_nonneg_left H hb.le, hbudget]
  refine ⟨(HF s hs).1, (HF s hs).2.1.trans hAC,
    (HF s hs).2.2.2.2.1.trans (mul_le_mul_of_nonneg_right hAC (by positivity)),
    (HF s hs).2.2.2.2.2.trans (by gcongr), ?_⟩
  intro i
  have HD := exitClockLogMultiplier_derivative_bound hs.1 hA0
    (fun r hr => (HF r (hsub hr)).1.of_le (by norm_num)) (fun r hr => (HF r (hsub hr)).2.2.1)
    (fun r hr => (HF r (hsub hr)).2.1) i
  have Hweak := exitClockLogMultiplier_weak_bound hs.1 hA hb.le
    (fun r hr => (HF r (hsub hr)).1.of_le (by norm_num)) (fun r hr => (HF r (hsub hr)).2.2.1)
    (fun r hr => (HF r (hsub hr)).2.1) (fun r hr => (HF r (hsub hr)).2.2.2.1)
    (fun r hr => (HF r (hsub hr)).2.2.2.2.2) i
  have Hpartial (j : Fin 3) : |fderiv ℝ (fun Z => exitClockLogMultiplier I i Z s) Y (Pi.single j 1)| ≤ C * s := by
    have H := ((fderiv ℝ (fun Z => exitClockLogMultiplier I i Z s) Y).le_opNorm (Pi.single j 1)).trans
      (mul_le_mul_of_nonneg_right HD.2 (norm_nonneg _))
    simp only [Real.norm_eq_abs, Pi.norm_single, norm_one, mul_one] at H
    exact H.trans (mul_le_mul_of_nonneg_right hLC hs.1)
  refine ⟨HD.1, Hpartial 0, Hpartial 1, Hweak.trans (mul_le_mul_of_nonneg_right hWC (by positivity)), ?_⟩
  apply Hweak.trans
  change _ ≤ 4096 * A ^ 2
  nlinarith only [mul_le_mul_of_nonneg_left hbs (sq_nonneg A), sq_nonneg A]

end BianchiIX
