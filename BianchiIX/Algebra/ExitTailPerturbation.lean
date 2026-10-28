import BianchiIX.Algebra.ExitTailBounds

noncomputable section

namespace BianchiIX

theorem exitTail_rate_differences {R u v w : ℝ}
    (ht : exitTailGap R v ≠ 0) (hd : exitTailSpeed R u v w ≠ 0) :
    exitTailStrongRate R u v w - exitTailStrongRate R 0 v 0 =
      (2 * v * w - w ^ 2 + u ^ 2 - 2 * coupling u v w * exitTailStrongRate R 0 v 0) /
        (2 * exitTailSpeed R u v w) ∧
    exitTailWeakRate R u v w - exitTailWeakRate R 0 v 0 =
      -coupling u v w * (1 + exitTailWeakRate R 0 v 0) / exitTailSpeed R u v w := by
  have hs : exitTailSpeed R 0 v 0 = exitTailGap R v := by simp [exitTailSpeed, coupling]
  simp only [exitTailStrongRate, exitTailWeakRate, hs, coupling, zero_mul, mul_zero,
    zero_pow (by norm_num : 2 ≠ 0), add_zero, sub_zero]
  constructor <;> field_simp <;> dsimp only [exitTailSpeed, coupling] <;> ring

theorem exitTail_boundary_rate_bounds {R v : ℝ}
    (hR : 7 / 4 ≤ R ∧ R ≤ 17 / 4) (hv : 0 ≤ v ∧ v ≤ 1) :
    |exitTailStrongRate R 0 v 0| ≤ 20 ∧ |exitTailWeakRate R 0 v 0| ≤ 7 := by
  obtain ⟨ht, htR⟩ := exitTailGap_compact hR.1 hv
  have ht0 : 0 < exitTailGap R v := by linarith only [ht]
  have hR2 : R ^ 2 ≤ 25 := by nlinarith only [hR.1, hR.2]
  have hs : exitTailSpeed R 0 v 0 = exitTailGap R v := by simp [exitTailSpeed, coupling]
  simp only [exitTailStrongRate, exitTailWeakRate, hs, coupling, zero_mul, mul_zero,
    zero_pow (by norm_num : 2 ≠ 0), add_zero, sub_zero, abs_div,
    abs_of_pos ht0, abs_of_pos (mul_pos (by norm_num : (0 : ℝ) < 2) ht0)]
  constructor
  · apply (div_le_iff₀ (mul_pos (by norm_num) ht0)).mpr
    apply (abs_sub _ _).trans
    rw [abs_of_nonneg (mul_nonneg (by norm_num) ht0.le), abs_of_nonneg (sq_nonneg R)]
    nlinarith only [hR2, ht]
  · apply (div_le_iff₀ ht0).mpr
    apply (abs_sub _ _).trans
    rw [abs_of_pos ht0, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith only [ht]

/-- Signed-wall perturbations preserve the vanishing orders needed for the long terminal tail. -/
theorem exitTail_perturbation_bounds {R u v w : ℝ}
    (hR : 7 / 4 ≤ R ∧ R ≤ 17 / 4) (hu : |u| ≤ 1 / 100)
    (hv : 0 ≤ v ∧ v ≤ 1) (hw : |w| ≤ 1 / 100) :
    |exitTailRadial R u v w| ≤ 20 * (|u| * v + (|u| + |w|) ^ 2) ∧
    |exitTailStrongRate R u v w - exitTailStrongRate R 0 v 0| ≤
      100 * ((|u| + |w|) * v + (|u| + |w|) ^ 2) ∧
    |exitTailWeakRate R u v w - exitTailWeakRate R 0 v 0| ≤
      100 * ((|u| + |w|) * v + (|u| + |w|) ^ 2) := by
  let b := |u| + |w|
  let H := b * v + b ^ 2
  have hb : 0 ≤ b := add_nonneg (abs_nonneg u) (abs_nonneg w)
  have hH : 0 ≤ H := add_nonneg (mul_nonneg hb hv.1) (sq_nonneg b)
  obtain ⟨ht, htR⟩ := exitTailGap_compact hR.1 hv
  have ht0 : 0 < exitTailGap R v := by linarith only [ht]
  have hR0 : 0 < R := by linarith only [hR.1]
  have hd := exitTailSpeed_compact hR.1 hu hv hw
  have hd0 : 0 < exitTailSpeed R u v w := by linarith only [hd]
  have hc := exitTail_coupling_bound (u := u) (w := w) hv.1
  have hcH : |coupling u v w| ≤ H := by
    have H' := mul_nonneg (abs_nonneg w) hv.1
    dsimp only [H, b]
    nlinarith only [hc, H']
  have hsq : (u - w) ^ 2 ≤ b ^ 2 := by
    have H' := abs_sub u w
    nlinarith only [H', sq_abs (u - w), abs_nonneg (u - w), hb]
  have hsum : |2 * v * w - w ^ 2 + u ^ 2| ≤ 2 * H := by
    have H' := (abs_add_le (2 * v * w - w ^ 2) (u ^ 2)).trans
      (add_le_add (abs_sub (2 * v * w) (w ^ 2)) le_rfl)
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
      abs_of_nonneg hv.1, abs_of_nonneg (sq_nonneg w), abs_of_nonneg (sq_nonneg u)] at H'
    have Huv := mul_nonneg (abs_nonneg u) hv.1
    have Huw := mul_nonneg (abs_nonneg u) (abs_nonneg w)
    dsimp only [H, b]
    nlinarith only [H', Huv, Huw, sq_abs u, sq_abs w, sq_nonneg |u|, sq_nonneg |w|]
  obtain ⟨hU, hW⟩ := exitTail_boundary_rate_bounds hR hv
  obtain ⟨dU, dW⟩ := exitTail_rate_differences (ne_of_gt ht0) (ne_of_gt hd0)
  refine ⟨?_, ?_, ?_⟩
  · rw [exitTailRadial, abs_div, abs_of_pos hd0]
    apply (div_le_iff₀ hd0).mpr
    have H' := abs_sub (-coupling u v w * R) (exitTailGap R v * (u - w) ^ 2 / R)
    rw [abs_mul, abs_neg, abs_of_pos hR0,
      abs_of_nonneg (div_nonneg (mul_nonneg ht0.le (sq_nonneg _)) hR0.le)] at H'
    have hquot : exitTailGap R v * (u - w) ^ 2 / R ≤ b ^ 2 := by
      apply (div_le_iff₀ hR0).mpr
      exact (mul_le_mul_of_nonneg_right htR (sq_nonneg _)).trans
        (by nlinarith only [mul_le_mul_of_nonneg_left hsq hR0.le])
    have hcoupled : |coupling u v w| * R ≤ 5 * (|u| * v + b ^ 2) := by
      have hR5 : R ≤ 5 := by linarith only [hR.2]
      have Hc := mul_le_mul hc hR5 hR0.le (add_nonneg (mul_nonneg (abs_nonneg u) hv.1) (sq_nonneg b))
      change _ ≤ (|u| * v + b ^ 2) * 5 at Hc
      linarith only [Hc]
    have hbase : 0 ≤ |u| * v + b ^ 2 := add_nonneg (mul_nonneg (abs_nonneg u) hv.1) (sq_nonneg b)
    have Hbudget := mul_le_mul_of_nonneg_left hd (mul_nonneg (by norm_num : (0 : ℝ) ≤ 20) hbase)
    nlinarith only [H', hquot, hcoupled, Hbudget, mul_nonneg (abs_nonneg u) hv.1]
  · rw [dU, abs_div, abs_of_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hd0)]
    apply (div_le_iff₀ (mul_pos (by norm_num) hd0)).mpr
    have H' := abs_sub (2 * v * w - w ^ 2 + u ^ 2) (2 * coupling u v w * exitTailStrongRate R 0 v 0)
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at H'
    have Hprod := mul_le_mul hcH hU (abs_nonneg _) hH
    have Hbudget := mul_le_mul_of_nonneg_left hd (mul_nonneg (by norm_num : (0 : ℝ) ≤ 100) hH)
    change _ ≤ 100 * H * (2 * exitTailSpeed R u v w)
    nlinarith only [H', hsum, Hprod, Hbudget, hH]
  · rw [dW, abs_div, abs_of_pos hd0, abs_mul, abs_neg]
    apply (div_le_iff₀ hd0).mpr
    have H' : |1 + exitTailWeakRate R 0 v 0| ≤ 8 := by
      have H'' := abs_add_le (1 : ℝ) (exitTailWeakRate R 0 v 0)
      rw [abs_one] at H''
      linarith only [H'', hW]
    have Hprod := mul_le_mul hcH H' (abs_nonneg _) hH
    have Hbudget := mul_le_mul_of_nonneg_left hd (mul_nonneg (by norm_num : (0 : ℝ) ≤ 100) hH)
    change _ ≤ 100 * H * exitTailSpeed R u v w
    nlinarith only [Hprod, Hbudget, hH]

/-- The boundary rates are integrably small: alpha plus radial drift plus V squared. -/
theorem exitTail_boundary_rate_small {R v α : ℝ} (hα : 0 ≤ α)
    (hR : 7 / 4 ≤ R ∧ R ≤ 17 / 4) (hv : 0 ≤ v ∧ v ≤ 1) :
    |exitTailStrongRate R 0 v 0| + |exitTailWeakRate R 0 v 0| ≤
      10 * (α + |R - (2 + 2 * α)| + v ^ 2) := by
  obtain ⟨ht, htR⟩ := exitTailGap_compact hR.1 hv
  have ht0 : 0 < exitTailGap R v := by linarith only [ht]
  have hR1 : 1 ≤ R := by linarith only [hR.1]
  have hR0 : 0 < R := by linarith only [hR1]
  have htv : v ^ 2 < R ^ 2 := by nlinarith only [hR.1, hv.1, hv.2]
  obtain ⟨hU, hW⟩ := exitTail_boundary_rates hR0 htv
  have hsum : 1 ≤ R + exitTailGap R v := by linarith only [ht, hR1]
  have hdu : 1 ≤ 2 * exitTailGap R v * (R + exitTailGap R v) := by
    have H := mul_le_mul ht hsum (by norm_num : (0 : ℝ) ≤ 1) ht0.le
    nlinarith only [H]
  have hrt : 1 ≤ R * exitTailGap R v := by
    nlinarith only [mul_le_mul hR1 ht (by norm_num : (0 : ℝ) ≤ 1) hR0.le]
  have hdw : 1 ≤ R * exitTailGap R v * (R + exitTailGap R v) := by
    nlinarith only [mul_le_mul hrt hsum (by norm_num : (0 : ℝ) ≤ 1) (mul_nonneg hR0.le ht0.le)]
  have hdu0 : 0 < 2 * exitTailGap R v * (R + exitTailGap R v) := by linarith only [hdu]
  have hdw0 : 0 < R * exitTailGap R v * (R + exitTailGap R v) := by linarith only [hdw]
  have huq : R * v ^ 2 / (2 * exitTailGap R v * (R + exitTailGap R v)) ≤ 5 * v ^ 2 := by
    apply (div_le_iff₀ hdu0).mpr
    have H := mul_le_mul_of_nonneg_left hdu (by positivity : 0 ≤ 5 * v ^ 2)
    have H' := mul_le_mul_of_nonneg_right hR.2 (sq_nonneg v)
    nlinarith only [H, H', sq_nonneg v]
  have hwq : 2 * v ^ 2 / (R * exitTailGap R v * (R + exitTailGap R v)) ≤ 2 * v ^ 2 := by
    apply (div_le_iff₀ hdw0).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hdw (by positivity : 0 ≤ 2 * v ^ 2)]
  have hUabs : |exitTailStrongRate R 0 v 0| ≤ |R - 2| / 2 + 5 * v ^ 2 := by
    rw [hU]
    have H := abs_sub (-(R - 2) / 2) (R * v ^ 2 / (2 * exitTailGap R v * (R + exitTailGap R v)))
    rw [abs_div, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2),
      abs_of_nonneg (div_nonneg (mul_nonneg hR0.le (sq_nonneg v)) hdu0.le)] at H
    linarith only [H, huq]
  have hWabs : |exitTailWeakRate R 0 v 0| ≤ |R - 2| + 2 * v ^ 2 := by
    rw [hW]
    have H := abs_sub ((R - 2) / R) (2 * v ^ 2 / (R * exitTailGap R v * (R + exitTailGap R v)))
    rw [abs_div, abs_of_pos hR0,
      abs_of_nonneg (div_nonneg (by positivity : 0 ≤ 2 * v ^ 2) hdw0.le)] at H
    have Hq : |R - 2| / R ≤ |R - 2| := (div_le_iff₀ hR0).mpr
      (by nlinarith only [mul_le_mul_of_nonneg_left hR1 (abs_nonneg (R - 2))])
    linarith only [H, Hq, hwq]
  have herr : |R - 2| ≤ |R - (2 + 2 * α)| + 2 * α := by
    have H := abs_add_le (R - (2 + 2 * α)) (2 * α)
    rw [show R - (2 + 2 * α) + 2 * α = R - 2 by ring,
      abs_of_nonneg (mul_nonneg (by norm_num) hα)] at H
    exact H
  linarith only [hUabs, hWabs, herr, hα, abs_nonneg (R - (2 + 2 * α)), sq_nonneg v]

end BianchiIX
