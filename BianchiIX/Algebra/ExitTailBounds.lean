import BianchiIX.Algebra.ExitTail

noncomputable section

namespace BianchiIX

theorem exitTailGap_compact {R v : ℝ} (hR : 7 / 4 ≤ R) (hv : 0 ≤ v ∧ v ≤ 1) :
    1 ≤ exitTailGap R v ∧ exitTailGap R v ≤ R := by
  have hR0 : 0 ≤ R := by linarith only [hR]
  have hv2 : v ^ 2 ≤ 1 := by nlinarith only [hv.1, hv.2]
  refine ⟨?_, ?_⟩
  · exact (Real.le_sqrt (by norm_num) (by nlinarith only [hR, hv2])).mpr
      (by nlinarith only [hR, hv2])
  · exact (Real.sqrt_le_left hR0).mpr (by nlinarith only [sq_nonneg v])

theorem exitTail_coupling_bound {u v w : ℝ} (hv : 0 ≤ v) :
    |coupling u v w| ≤ |u| * v + (|u| + |w|) ^ 2 := by
  have H : |v + w - u| ≤ v + |w| + |u| := by
    exact (abs_sub _ _).trans (add_le_add ((abs_add_le v w).trans_eq (by rw [abs_of_nonneg hv])) le_rfl)
  rw [coupling, abs_mul]
  have H' := mul_le_mul_of_nonneg_left H (abs_nonneg u)
  nlinarith only [H', mul_nonneg (abs_nonneg u) (abs_nonneg w), sq_nonneg |w|]

/-- A signed wall box has a uniform positive clock even as the terminal gap tends to zero. -/
theorem exitTailSpeed_compact {R u v w : ℝ} (hR : 7 / 4 ≤ R)
    (hu : |u| ≤ 1 / 100) (hv : 0 ≤ v ∧ v ≤ 1) (hw : |w| ≤ 1 / 100) :
    1 / 2 ≤ exitTailSpeed R u v w := by
  have ht := (exitTailGap_compact hR hv).1
  have hc := exitTail_coupling_bound (u := u) (w := w) hv.1
  have huv : |u| * v ≤ 1 / 100 := by
    nlinarith only [mul_le_mul_of_nonneg_left hv.2 (abs_nonneg u), hu]
  have hb : (|u| + |w|) ^ 2 ≤ (1 / 50 : ℝ) ^ 2 := by
    nlinarith only [hu, hw, abs_nonneg u, abs_nonneg w]
  have H := neg_abs_le (coupling u v w)
  dsimp only [exitTailSpeed]
  linarith only [ht, hc, huv, hb, H]

theorem exitTailRadial_nonpos {R u v w : ℝ} (hR : 0 < R) (ht : 0 ≤ exitTailGap R v)
    (hc : 0 ≤ coupling u v w) (hd : 0 < exitTailSpeed R u v w) :
    exitTailRadial R u v w ≤ 0 := by
  apply div_nonpos_of_nonpos_of_nonneg _ hd.le
  exact sub_nonpos.mpr (le_trans (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc) hR.le)
    (div_nonneg (mul_nonneg ht (sq_nonneg _)) hR.le))

/-- Positive tails have the small weak-wall growth rate used in D.12. -/
theorem exitTailWeakRate_le {R u v w α : ℝ} (hα : 0 ≤ α)
    (ht : 1 ≤ exitTailGap R v) (htR : exitTailGap R v ≤ R)
    (hR : R ≤ 2 + 2 * α) (hc : 0 ≤ coupling u v w) :
    exitTailWeakRate R u v w ≤ α / (1 + α) := by
  have ht0 : 0 < exitTailGap R v := by linarith only [ht]
  have hd : 0 < exitTailSpeed R u v w := add_pos_of_pos_of_nonneg ht0 hc
  have hcorr := exitTailWeakRate_correction (ne_of_gt ht0) (ne_of_gt hd)
  have hneg : -2 * coupling u v w * (exitTailGap R v - 1) /
      (exitTailGap R v * exitTailSpeed R u v w) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (by norm_num) hc) (by linarith only [ht]))
      (mul_pos ht0 hd).le
  have hα0 : 0 < 1 + α := by linarith only [hα]
  have hbound : 1 - 2 / exitTailGap R v ≤ α / (1 + α) := by
    apply (le_div_iff₀ hα0).mpr
    apply (mul_le_mul_iff_left₀ ht0).mp
    field_simp
    nlinarith only [htR, hR]
  linarith only [hcorr, hneg, hbound]

end BianchiIX
