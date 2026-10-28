import BianchiIX.Algebra.ExitCyclePhase

noncomputable section

namespace BianchiIX

/-- Finite differences in a cyclic quotient lose two powers of the terminal parameter. -/
theorem exitCycle_quotient_difference {α B H H₀ n n₀ : ℝ} (hα : 0 < α) (hB : 0 ≤ B)
    (hH : 3 * α ^ 2 ≤ H) (hH₀ : 3 * α ^ 2 ≤ H₀)
    (hHd : |H - H₀| ≤ 20 * α * B) (hn : |n - n₀| ≤ 12 * B) (hn₀ : |n₀| ≤ 12 * α) :
    |n / H - n₀ / H₀| ≤ 40 * B / α ^ 2 := by
  have hHp : 0 < H := lt_of_lt_of_le (by positivity) hH
  have hH₀p : 0 < H₀ := lt_of_lt_of_le (by positivity) hH₀
  have heq : n / H - n₀ / H₀ = (n - n₀) / H + n₀ * (H₀ - H) / (H * H₀) := by field_simp; ring
  have HE := abs_add_le ((n - n₀) / H) (n₀ * (H₀ - H) / (H * H₀))
  rw [← heq] at HE
  simp only [abs_div, abs_mul, abs_of_pos hHp, abs_of_pos hH₀p, abs_sub_comm H₀ H] at HE
  have HN : |n / H - n₀ / H₀| ≤ 12 * B / H + (12 * α) * (20 * α * B) / (H * H₀) := by
    apply HE.trans
    gcongr
  have H1 : 12 * B / H ≤ 4 * B / α ^ 2 := by
    apply (div_le_div_iff₀ hHp (sq_pos_of_pos hα)).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hH hB]
  have HH : 9 * α ^ 4 ≤ H * H₀ := by
    have H := mul_le_mul hH hH₀ (by positivity : 0 ≤ 3 * α ^ 2) hHp.le
    nlinarith only [H]
  have H2 : (12 * α) * (20 * α * B) / (H * H₀) ≤ 30 * B / α ^ 2 := by
    calc
      _ ≤ (12 * α) * (20 * α * B) / (9 * α ^ 4) := div_le_div_of_nonneg_left (by positivity) (by positivity) HH
      _ ≤ _ := by
        apply (div_le_div_iff₀ (by positivity : 0 < 9 * α ^ 4) (sq_pos_of_pos hα)).mpr
        nlinarith only [mul_nonneg (pow_nonneg hα.le 4) hB]
  have HB : 0 ≤ B / α ^ 2 := div_nonneg hB (sq_nonneg α)
  simp only [mul_div_assoc] at HN H1 H2 ⊢
  linarith only [HN, H1, H2, HB]

theorem exitCycle_reference_denom_difference {α B R u v w : ℝ} (hα : 0 < α ∧ α ≤ 1)
    (hB : B ≤ α / 10000) (hR : |R - (2 + 2 * α)| ≤ B)
    (hw : |u| + |w| ≤ B) (hv : 0 ≤ v ∧ v ≤ α / 100) :
    |exitTailGap R v - exitTailGap (2 + 2 * α) v| ≤ 3 * B ∧
      |axisCycleDenom (1 - exitTailGap R v) u v w -
        axisCycleDenom (1 - exitTailGap (2 + 2 * α) v) 0 v 0| ≤ 20 * α * B := by
  let R₀ := 2 + 2 * α
  let t := exitTailGap R v
  let t₀ := exitTailGap R₀ v
  have hα0 : 0 < α := hα.1
  have hB0 : 0 ≤ B := (add_nonneg (abs_nonneg _) (abs_nonneg _)).trans hw
  have hRc := abs_le.mp hR
  have hRlo : 7 / 4 ≤ R := by linarith only [hRc.1, hB, hα.1]
  have hR₀lo : 7 / 4 ≤ R₀ := by dsimp only [R₀]; linarith only [hα.1]
  have hv1 : v ≤ 1 := by linarith only [hv.2, hα.2]
  have HD := exitTailGap_terminal_offset hα hB hR hv
  have HD₀ := exitTailGap_terminal_offset hα (B := 0) (by positivity) (R := R₀) (by simp [R₀]) hv
  have hts : 3 ≤ t + t₀ := by dsimp only [t, t₀]; linarith only [HD.1, HD₀.1, hα.1]
  have hRs : 0 < R + R₀ := by linarith only [hRlo, hR₀lo]
  have hRs9 : R + R₀ ≤ 9 := by dsimp only [R₀]; linarith only [hRc.2, hB, hα.2]
  have hsq := exitTailGap_sq (by nlinarith only [hRlo, hv.1, hv1] : v ^ 2 ≤ R ^ 2)
  have hsq₀ := exitTailGap_sq (by nlinarith only [hR₀lo, hv.1, hv1] : v ^ 2 ≤ R₀ ^ 2)
  have hid : (t - t₀) * (t + t₀) = (R - R₀) * (R + R₀) := by dsimp only [t, t₀]; nlinarith only [hsq, hsq₀]
  have Habs := congrArg abs hid
  rw [abs_mul, abs_mul, abs_of_nonneg (show 0 ≤ t + t₀ by linarith only [hts]), abs_of_pos hRs] at Habs
  have HG : |t - t₀| ≤ 3 * B := by
    have H1 := mul_le_mul_of_nonneg_right hR hRs.le
    have H2 := mul_le_mul_of_nonneg_left hRs9 hB0
    have H3 := mul_le_mul_of_nonneg_left hts (abs_nonneg (t - t₀))
    change |R - R₀| * (R + R₀) ≤ B * (R + R₀) at H1
    nlinarith only [Habs, H1, H2, H3]
  have hsum : 0 ≤ (t - 2) + (t₀ - 2) ∧ (t - 2) + (t₀ - 2) ≤ 6 * α := by
    dsimp only [t, t₀]
    constructor <;> linarith only [HD.1, HD.2, HD₀.1, HD₀.2, hα.1]
  have HW := exitCycle_terminal_wall_error hB hw hv (m := 1 - t)
  have heq : axisCycleDenom (1 - t) u v w - axisCycleDenom (1 - t₀) 0 v 0 =
      (axisCycleDenom (1 - t) u v w - ((1 - t + 1) ^ 2 + v ^ 2)) + (t - t₀) * ((t - 2) + (t₀ - 2)) := by
    unfold axisCycleDenom curvature
    ring
  have HE := abs_add_le (axisCycleDenom (1 - t) u v w - ((1 - t + 1) ^ 2 + v ^ 2))
    ((t - t₀) * ((t - 2) + (t₀ - 2)))
  rw [← heq, abs_mul, abs_of_nonneg hsum.1] at HE
  have HP := mul_le_mul HG hsum.2 hsum.1 (by positivity : 0 ≤ 3 * B)
  refine ⟨HG, ?_⟩
  nlinarith only [HE, HW, HP, mul_nonneg hα.1.le hB0]

theorem exitCycle_reference_coordinate_difference {α B R u v w : ℝ} (hα : 0 < α ∧ α ≤ 1)
    (hB : B ≤ α / 10000) (hR : |R - (2 + 2 * α)| ≤ B)
    (hw : |u| + |w| ≤ B) (hv : 0 ≤ v ∧ v ≤ α / 100) :
    let t := exitTailGap R v
    let t₀ := exitTailGap (2 + 2 * α) v
    let H := axisCycleDenom (1 - t) u v w
    let H₀ := axisCycleDenom (1 - t₀) 0 v 0
    |(1 - 4 * (2 - t) / H) - (1 - 4 * (2 - t₀) / H₀)| ≤ 40 * B / α ^ 2 ∧
      |4 * v / H - 4 * v / H₀| ≤ 40 * B / α ^ 2 := by
  intro t t₀ H H₀
  have hα0 : 0 < α := hα.1
  have hB0 : 0 ≤ B := (add_nonneg (abs_nonneg _) (abs_nonneg _)).trans hw
  have HD := exitCycle_reference_denom_difference hα hB hR hw hv
  have HH := (exitCycleDenom_terminal_bounds hα hB hR hw hv).1
  have HH₀ := (exitCycleDenom_terminal_bounds hα (B := 0) (R := 2 + 2 * α) (by positivity) (by simp)
    (by norm_num : |(0 : ℝ)| + |(0 : ℝ)| ≤ 0) hv).1
  have hH : 3 * α ^ 2 ≤ H := by dsimp only [H, t]; nlinarith only [HH, sq_nonneg α]
  have hH₀ : 3 * α ^ 2 ≤ H₀ := by dsimp only [H₀, t₀]; nlinarith only [HH₀, sq_nonneg α]
  have HT := exitTailGap_terminal_offset hα (B := 0) (R := 2 + 2 * α) (by positivity) (by simp) hv
  have ht₀ : 0 ≤ t₀ - 2 ∧ t₀ - 2 ≤ 3 * α := by dsimp only [t₀]; constructor <;> linarith only [HT.1, HT.2, hα.1]
  have Hm := exitCycle_quotient_difference hα.1 hB0 hH hH₀ HD.2
    (n := 4 * (t - 2)) (n₀ := 4 * (t₀ - 2))
    (by rw [show 4 * (t - 2) - 4 * (t₀ - 2) = 4 * (t - t₀) by ring, abs_mul,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]; linarith only [HD.1])
    (by rw [abs_of_nonneg (mul_nonneg (by norm_num) ht₀.1)]; linarith only [ht₀.2])
  have Hu := exitCycle_quotient_difference hα.1 hB0 hH hH₀ HD.2
    (n := 4 * v) (n₀ := 4 * v) (by simp; positivity)
    (by rw [abs_of_nonneg (mul_nonneg (by norm_num) hv.1)]; linarith only [hv.2, hα.1])
  refine ⟨?_, Hu⟩
  convert Hm using 1
  congr 1
  ring

/-- A reciprocal phase estimate keeps the same constant once the perturbation is smaller than α. -/
theorem terminal_phase_reciprocal {α κ d : ℝ} (hα : 0 < α) (hsmall : d ≤ α)
    (herr : |κ - 2 / α| ≤ d / α ^ 2) :
    1 / α ≤ κ ∧ |2 / κ - α| ≤ d ∧ (d < 1 - α → 2 / κ < 1 ∧ 2 < κ) := by
  have hdiv : d / α ^ 2 ≤ α / α ^ 2 := div_le_div_of_nonneg_right hsmall (sq_nonneg α)
  have heq : 2 / α - α / α ^ 2 = 1 / α := by field_simp; ring
  have hk : 1 / α ≤ κ := by linarith only [(abs_le.mp herr).1, hdiv, heq]
  have hk0 : 0 < κ := lt_of_lt_of_le (by positivity) hk
  have hκα : 1 ≤ κ * α := (div_le_iff₀ hα).mp hk
  have hfactor : α / κ ≤ α ^ 2 := by
    apply (div_le_iff₀ hk0).mpr
    nlinarith only [mul_le_mul_of_nonneg_right hκα hα.le]
  have hid : 2 / κ - α = -(α / κ) * (κ - 2 / α) := by field_simp; ring
  have HE : |2 / κ - α| ≤ d := by
    rw [hid, abs_mul, abs_neg, abs_of_pos (div_pos hα hk0)]
    calc
      _ ≤ α ^ 2 * (d / α ^ 2) := mul_le_mul hfactor herr (abs_nonneg _) (sq_nonneg α)
      _ = d := by field_simp
  refine ⟨hk, HE, ?_⟩
  intro hbranch
  have hx : 2 / κ < 1 := by linarith only [(abs_le.mp HE).2, hbranch]
  exact ⟨hx, by simpa only [one_mul] using (div_lt_iff₀ hk0).mp hx⟩

end BianchiIX
