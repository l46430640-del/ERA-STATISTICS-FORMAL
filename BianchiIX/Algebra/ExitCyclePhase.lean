import BianchiIX.Algebra.ExitCycleEndpoint

noncomputable section

namespace BianchiIX

theorem exitTailGap_terminal_error {α B R v : ℝ} (hα : 0 < α ∧ α ≤ 1)
    (hB : B ≤ α / 10000) (hR : |R - (2 + 2 * α)| ≤ B) (hv : 0 ≤ v ∧ v ≤ α / 100) :
    |exitTailGap R v - 2 - 2 * α| ≤ B + v ^ 2 / 3 := by
  have hRc := abs_le.mp hR
  have hRlo : 7 / 4 ≤ R := by linarith only [hRc.1, hB, hα.1]
  have hv1 : v ≤ 1 := by linarith only [hv.2, hα.2]
  have ht := exitTailGap_compact hRlo ⟨hv.1, hv1⟩
  have hp : 3 ≤ R + exitTailGap R v := by linarith only [hRc.1, hB, hα.1, ht.1]
  have hp0 : 0 < R + exitTailGap R v := lt_of_lt_of_le (by norm_num) hp
  have hvR : v ^ 2 ≤ R ^ 2 := by nlinarith only [hRlo, hv.1, hv1]
  have hs := exitTailGap_sq hvR
  have heq : exitTailGap R v - R = -(v ^ 2 / (R + exitTailGap R v)) := by
    field_simp
    nlinarith only [hs]
  have hsmall : v ^ 2 / (R + exitTailGap R v) ≤ v ^ 2 / 3 := by
    apply (div_le_div_iff₀ hp0 (by norm_num)).mpr
    nlinarith only [mul_le_mul_of_nonneg_right hp (sq_nonneg v)]
  have HE := abs_add_le (R - (2 + 2 * α)) (exitTailGap R v - R)
  have hsum : R - (2 + 2 * α) + (exitTailGap R v - R) = exitTailGap R v - 2 - 2 * α := by ring
  rw [hsum] at HE
  rw [heq, abs_neg, abs_of_nonneg (div_nonneg (sq_nonneg v) hp0.le)] at HE
  exact HE.trans (add_le_add hR hsmall)

theorem exitCycle_terminal_wall_error {α B m u v w : ℝ}
    (hB : B ≤ α / 10000) (hw : |u| + |w| ≤ B) (hv : 0 ≤ v ∧ v ≤ α / 100) :
    |axisCycleDenom m u v w - ((m + 1) ^ 2 + v ^ 2)| ≤ α * B := by
  have hB0 : 0 ≤ B := (add_nonneg (abs_nonneg _) (abs_nonneg _)).trans hw
  have H := axisCycleDenom_wall_error m u v w
  rw [abs_of_nonneg hv.1] at H
  have hs : (|u| + |w|) ^ 2 ≤ B ^ 2 :=
    (sq_le_sq₀ (add_nonneg (abs_nonneg _) (abs_nonneg _)) hB0).mpr hw
  have hc := mul_le_mul_of_nonneg_left hw (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hv.1)
  have hBsq := mul_le_mul_of_nonneg_right hB hB0
  have hcross := mul_le_mul_of_nonneg_right hv.2 hB0
  nlinarith only [H, hs, hc, hBsq, hcross]

/-- The cyclic phase error has only radial drift and the square of the auxiliary height. -/
theorem exitCycle_terminal_phase_error {α B R u v w : ℝ} (hα : 0 < α ∧ α ≤ 1)
    (hB : B ≤ α / 10000) (hR : |R - (2 + 2 * α)| ≤ B)
    (hw : |u| + |w| ≤ B) (hv : 0 ≤ v ∧ v ≤ α / 100) :
    |(1 - 4 * (2 - exitTailGap R v) / axisCycleDenom (1 - exitTailGap R v) u v w) - (1 + 2 / α)| ≤
      4 * (B / α ^ 2 + v ^ 2 / α ^ 3) := by
  let d := exitTailGap R v - 2
  let H := axisCycleDenom (1 - exitTailGap R v) u v w
  have hα0 : 0 < α := hα.1
  have hB0 : 0 ≤ B := (add_nonneg (abs_nonneg _) (abs_nonneg _)).trans hw
  have HD := exitTailGap_terminal_offset hα hB hR hv
  have hd : 0 ≤ d ∧ d ≤ 3 * α := by dsimp only [d]; constructor <;> linarith only [HD.1, HD.2, hα.1]
  have HE : |d - 2 * α| ≤ B + v ^ 2 / 3 := exitTailGap_terminal_error hα hB hR hv
  have HW : |H - (d ^ 2 + v ^ 2)| ≤ α * B := by
    have H0 := exitCycle_terminal_wall_error hB hw hv (m := 1 - exitTailGap R v)
    convert H0 using 1
    dsimp only [H, d]
    ring_nf
  have HH := (exitCycleDenom_terminal_bounds hα hB hR hw hv).1
  have hH : 3 * α ^ 2 ≤ H := by dsimp only [H]; nlinarith only [HH, sq_nonneg α]
  have hH0 : 0 < H := lt_of_lt_of_le (by positivity) hH
  have Hnum : |4 * α * d - 2 * H| ≤ 8 * α * B + 4 * v ^ 2 := by
    have H1 := abs_add_le (-2 * d * (d - 2 * α)) (-2 * v ^ 2)
    have H2 := abs_add_le (-2 * d * (d - 2 * α) + -2 * v ^ 2) (-2 * (H - (d ^ 2 + v ^ 2)))
    have HI : -2 * d * (d - 2 * α) + -2 * v ^ 2 + -2 * (H - (d ^ 2 + v ^ 2)) = 4 * α * d - 2 * H := by ring
    rw [HI] at H2
    simp only [abs_mul, abs_of_nonneg hd.1, abs_of_nonneg (sq_nonneg v), abs_neg,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at H1 H2
    have HP := mul_le_mul_of_nonneg_left HE (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hd.1)
    have HQ := mul_le_mul_of_nonneg_right hd.2 (by positivity : 0 ≤ B + v ^ 2 / 3)
    have HV := mul_le_mul_of_nonneg_right hα.2 (sq_nonneg v)
    nlinarith only [H1, H2, HP, HQ, HW, HV]
  have heq : (1 - 4 * (2 - exitTailGap R v) / H) - (1 + 2 / α) = (4 * α * d - 2 * H) / (α * H) := by
    dsimp only [d]
    field_simp
    ring
  change |(1 - 4 * (2 - exitTailGap R v) / H) - (1 + 2 / α)| ≤ _
  rw [heq, abs_div, abs_of_pos (mul_pos hα.1 hH0)]
  calc
    _ ≤ (8 * α * B + 4 * v ^ 2) / (α * H) := div_le_div_of_nonneg_right Hnum (mul_pos hα.1 hH0).le
    _ ≤ (8 * α * B + 4 * v ^ 2) / (3 * α ^ 3) := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      nlinarith only [mul_le_mul_of_nonneg_left hH hα.1.le]
    _ ≤ 4 * (B / α ^ 2 + v ^ 2 / α ^ 3) := by
      apply (div_le_iff₀ (by positivity : 0 < 3 * α ^ 3)).mpr
      field_simp
      nlinarith only [mul_nonneg hα.1.le hB0, sq_nonneg v]

end BianchiIX
