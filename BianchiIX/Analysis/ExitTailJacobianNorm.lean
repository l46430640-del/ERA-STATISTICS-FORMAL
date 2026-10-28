import BianchiIX.Analysis.ExitTailJacobian

noncomputable section

namespace BianchiIX

private theorem abs_three_dot_le {a ξ : Fin 3 → ℝ} {A B C : ℝ}
    (h0 : |a 0| ≤ A) (h1 : |a 1| ≤ B) (h2 : |a 2| ≤ C) :
    |∑ i : Fin 3, a i * ξ i| ≤ (A + B + C) * ‖ξ‖ := by
  have hx (i : Fin 3) : |ξ i| ≤ ‖ξ‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm ξ i
  have H := Finset.abs_sum_le_sum_abs (fun i : Fin 3 => a i * ξ i) Finset.univ
  simp only [abs_mul] at H
  have H0 := mul_le_mul h0 (hx 0) (abs_nonneg _) ((abs_nonneg _).trans h0)
  have H1 := mul_le_mul h1 (hx 1) (abs_nonneg _) ((abs_nonneg _).trans h1)
  have H2 := mul_le_mul h2 (hx 2) (abs_nonneg _) ((abs_nonneg _).trans h2)
  simp [Fin.sum_univ_succ] at H ⊢
  nlinarith only [H, H0, H1, H2]

/-- Its integrable norm bound gives ordinary variational control without a long-time exponential loss. -/
theorem exitTailField_jacobian_norm_bound {v : ℝ} {Y : ExitTailState}
    (hR : 7 / 4 ≤ Y 0 ∧ Y 0 ≤ 17 / 4) (hu : |Y 1| ≤ 1 / 100)
    (hv : 0 ≤ v ∧ v ≤ 1) (hw : |Y 2| ≤ 1 / 100) :
    ‖fderiv ℝ (exitTailField v) Y‖ ≤
      |exitTailWallRate v Y 0| + |exitTailWallRate v Y 1| + 2048 * (v + |Y 1| + |Y 2|) := by
  let b := |Y 1| + |Y 2|
  let H := |Y 1| * v + b ^ 2
  have hb : 0 ≤ b := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hb1 : b ≤ 1 := by dsimp only [b]; linarith only [hu, hw]
  have hB : 0 ≤ v + b := add_nonneg hv.1 hb
  have hB2 : v + b ≤ 2 := by linarith only [hv.2, hb1]
  have hH : H ≤ v + b := by
    have HU : |Y 1| ≤ 1 := hu.trans (by norm_num)
    have Hv := mul_le_mul_of_nonneg_right HU hv.1
    have Hsq : b ^ 2 ≤ b := by nlinarith only [hb, hb1]
    dsimp only [H]
    nlinarith only [Hv, Hsq]
  have hR0 : 0 < Y 0 := by linarith only [hR.1]
  have hvR : v ^ 2 < (Y 0) ^ 2 := by nlinarith only [hR.1, hv.1, hv.2]
  have hd : exitTailSpeed (Y 0) (Y 1) v (Y 2) ≠ 0 := by
    have H := exitTailSpeed_compact hR.1 hu hv hw
    linarith only [H]
  have HR := exitTail_radial_gradient_bounds hR hu hv hw
  apply ContinuousLinearMap.opNorm_le_bound _ (by
    have H0 := abs_nonneg (exitTailWallRate v Y 0)
    have H1 := abs_nonneg (exitTailWallRate v Y 1)
    change 0 ≤ _ + _ + 2048 * (v + |Y 1| + |Y 2|)
    dsimp only [b] at hB
    linarith only [H0, H1, hB])
  intro ξ
  have hn : 0 ≤ ‖ξ‖ := norm_nonneg _
  have hrad : |∑ i : Fin 3, exitTailRadialGradient (Y 0) (Y 1) v (Y 2) i * ξ i| ≤
      512 * (v + b) * ‖ξ‖ := by
    have Hdot := abs_three_dot_le (ξ := ξ) HR.1 HR.2.1 HR.2.2
    have Hsum : 256 * H + 32 * (v + b) + 16 * b ≤ 512 * (v + b) := by
      linarith only [hH, hv.1, hb]
    have HH := mul_le_mul_of_nonneg_right Hsum hn
    dsimp only [H, b] at HH ⊢
    nlinarith only [Hdot, HH]
  have hrate (i : Fin 2) : |∑ j : Fin 3, exitTailRateGradient v Y i j * ξ j| ≤ 1536 * ‖ξ‖ := by
    have HI := exitTailRateGradient_bounds hR hu hv hw i
    have Hdot := abs_three_dot_le (ξ := ξ) HI.1 (HI.2 0) (HI.2 1)
    have Hsum : 512 + 256 * (v + b) + 256 * (v + b) ≤ 1536 := by linarith only [hB2]
    have HH := mul_le_mul_of_nonneg_right Hsum hn
    dsimp only [b] at HH
    nlinarith only [Hdot, HH]
  have hcoord (i : Fin 3) : |ξ i| ≤ ‖ξ‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm ξ i
  have hwall (i : Fin 2) :
      |Y i.succ * (∑ j : Fin 3, exitTailRateGradient v Y i j * ξ j) + exitTailWallRate v Y i * ξ i.succ| ≤
        (|exitTailWallRate v Y 0| + |exitTailWallRate v Y 1| + 2048 * (v + b)) * ‖ξ‖ := by
    have hYb : |Y i.succ| ≤ b := by fin_cases i <;> dsimp [b] <;> linarith [abs_nonneg (Y 1), abs_nonneg (Y 2)]
    have ha : |exitTailWallRate v Y i| ≤ |exitTailWallRate v Y 0| + |exitTailWallRate v Y 1| := by
      fin_cases i
      · exact le_add_of_nonneg_right (abs_nonneg (exitTailWallRate v Y 1))
      · exact le_add_of_nonneg_left (abs_nonneg (exitTailWallRate v Y 0))
    have H0 := mul_le_mul hYb (hrate i) (abs_nonneg _) hb
    have H1 := mul_le_mul ha (hcoord i.succ) (abs_nonneg _)
      (add_nonneg (abs_nonneg _) (abs_nonneg _))
    have Htri := abs_add_le
      (Y i.succ * (∑ j : Fin 3, exitTailRateGradient v Y i j * ξ j)) (exitTailWallRate v Y i * ξ i.succ)
    simp only [abs_mul] at Htri
    have Hsmall := mul_nonneg hv.1 hn
    have Hsmall' := mul_nonneg hb hn
    nlinarith only [Htri, H0, H1, Hsmall, Hsmall']
  rw [exitTailField_fderiv hR0 hvR hd]
  apply (pi_norm_le_iff_of_nonempty _).mpr
  intro i
  rw [Real.norm_eq_abs]
  fin_cases i
  · change |∑ i : Fin 3, exitTailRadialGradient (Y 0) (Y 1) v (Y 2) i * ξ i| ≤ _
    have HH : 512 * (v + b) ≤
        |exitTailWallRate v Y 0| + |exitTailWallRate v Y 1| + 2048 * (v + b) := by
      linarith only [hB, abs_nonneg (exitTailWallRate v Y 0), abs_nonneg (exitTailWallRate v Y 1)]
    have Hmul := mul_le_mul_of_nonneg_right HH hn
    dsimp only [b] at hrad Hmul
    nlinarith only [hrad, Hmul]
  · simpa [exitTailLinearization, exitTailRateGradient, exitTailWallRate, b, add_assoc] using hwall 0
  · simpa [exitTailLinearization, exitTailRateGradient, exitTailWallRate, b, add_assoc] using hwall 1

end BianchiIX
