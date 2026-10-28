import BianchiIX.Dynamics.TerminalPhaseStatistics

noncomputable section

namespace BianchiIX

theorem terminal_phase_cone_direction (L : ExitTailState →L[ℝ] ℝ) (d : ExitTailState)
    {α C b u w : ℝ} (hα : 0 < α) (hC : 0 ≤ C) (hb : 0 ≤ b)
    (hsmall : b ≤ α ^ 2) (hu : 0 ≤ u) (hw : 0 ≤ w) (hsum : u + w ≤ b)
    (hd0 : d 0 = 1) (hd1 : |d 1| ≤ Real.sqrt u) (hd2 : |d 2| ≤ Real.sqrt w)
    (hrad : |L (Pi.single 0 1) + 1 / α ^ 2| ≤ C * b / α ^ 3)
    (hwall : |L (Pi.single 1 1)| + |L (Pi.single 2 1)| ≤ C / α ^ 2) :
    |α ^ 2 * L d + 1| ≤ 2 * C * Real.sqrt b := by
  let Q : ExitTailState →L[ℝ] ℝ := α ^ 2 • L + ContinuousLinearMap.proj 0
  have HQd : Q d = α ^ 2 * L d + 1 := by simp [Q, hd0]
  have HQ0 : Q (Pi.single 0 1) = α ^ 2 * (L (Pi.single 0 1) + 1 / α ^ 2) := by
    simp only [Q, add_apply, smul_apply, smul_eq_mul, ContinuousLinearMap.proj_apply, Pi.single_eq_same]
    field_simp
  have HQ1 : Q (Pi.single 1 1) = α ^ 2 * L (Pi.single 1 1) := by simp [Q]
  have HQ2 : Q (Pi.single 2 1) = α ^ 2 * L (Pi.single 2 1) := by simp [Q]
  have Hr : |Q (Pi.single 0 1)| ≤ C * b / α := by
    rw [HQ0, abs_mul, abs_of_nonneg (sq_nonneg α)]
    exact (mul_le_mul_of_nonneg_left hrad (sq_nonneg α)).trans_eq (by field_simp)
  have Hw : |Q (Pi.single 1 1)| + |Q (Pi.single 2 1)| ≤ C := by
    rw [HQ1, HQ2, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg α), ← mul_add]
    exact (mul_le_mul_of_nonneg_left hwall (sq_nonneg α)).trans_eq (by field_simp)
  have hroot : Real.sqrt b ≤ α := Real.sqrt_le_iff.mpr ⟨hα.le, hsmall⟩
  have Hb : b / α ≤ Real.sqrt b := (div_le_iff₀ hα).mpr (by
    have H := mul_le_mul_of_nonneg_left hroot (Real.sqrt_nonneg b)
    nlinarith only [H, Real.sq_sqrt hb])
  have H1 : |d 1| ≤ Real.sqrt b := hd1.trans (Real.sqrt_le_sqrt (by linarith only [hsum, hw]))
  have H2 : |d 2| ≤ Real.sqrt b := hd2.trans (Real.sqrt_le_sqrt (by linarith only [hsum, hu]))
  have H := clm_three_coordinate_bound Q d
  rw [HQd, hd0, abs_one, one_mul] at H
  have Hwall : |d 1| * |Q (Pi.single 1 1)| + |d 2| * |Q (Pi.single 2 1)| ≤ Real.sqrt b * C := by
    calc
      _ ≤ Real.sqrt b * |Q (Pi.single 1 1)| + Real.sqrt b * |Q (Pi.single 2 1)| := by gcongr
      _ = Real.sqrt b * (|Q (Pi.single 1 1)| + |Q (Pi.single 2 1)|) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left Hw (Real.sqrt_nonneg b)
  have Hr' : |Q (Pi.single 0 1)| ≤ C * Real.sqrt b := Hr.trans (by
    simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left Hb hC)
  nlinarith only [H, Hwall, Hr']

/-- The actual phase reverses every normalized square-root cone direction, with (D.34) error. -/
theorem exists_terminal_phase_cone_bounds :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η₀ : ℝ, (0 < η₀ ∧ η₀ ≤ δ) →
      ∀ J : ℕ, 4 ≤ J → ∃ C ≥ (1 : ℝ), ∃ ε > (0 : ℝ), ∀ η α b u w : ℝ,
      η₀ ≤ η → η ≤ δ → (0 < α ∧ α ≤ 1) →
      0 < b → b ≤ ε * α ^ (2 * J) → |u| + |w| ≤ b → 0 < u → 0 < w →
      let Y : ExitTailState := ![2 + 2 * α, u, w]
      let h := η * α ^ J
      coreTailValid h Y ∧ ContDiffAt ℝ 2 (terminalConnectionPhase h) Y ∧
        C * Real.sqrt b ≤ 1 / 4 ∧ ∀ d : ExitTailState,
          d 0 = 1 → |d 1| ≤ Real.sqrt u → |d 2| ≤ Real.sqrt w →
          |α ^ 2 * fderiv ℝ (terminalConnectionPhase h) Y d + 1| ≤ C * Real.sqrt b ∧
          fderiv ℝ (terminalConnectionPhase h) Y d < 0 ∧
          3 / (4 * α ^ 2) ≤ |fderiv ℝ (terminalConnectionPhase h) Y d| := by
  obtain ⟨δ, hδ, hδhi, HE⟩ := exists_terminal_phase_statistics
  refine ⟨δ, hδ, hδhi, ?_⟩
  intro η₀ hη₀ J hJ
  obtain ⟨A, hA, ε₀, hε₀, HA⟩ := HE η₀ hη₀ J hJ
  let C := 2 * A
  have hC : 1 ≤ C := by dsimp only [C]; linarith only [hA]
  have hC0 : 0 < C := lt_of_lt_of_le (by norm_num) hC
  let a := 1 / (4 * C)
  have ha : 0 < a := by dsimp only [a]; positivity
  let ε := min ε₀ (min 1 (a ^ 2))
  refine ⟨C, hC, ε, lt_min hε₀ (lt_min (by norm_num) (sq_pos_of_pos ha)), ?_⟩
  intro η α b u w hηlo hηhi hα hb hsmall hsum hu hw Y h
  have hε1 : ε ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hbε : b ≤ ε := hsmall.trans (mul_le_of_le_one_right
    (le_of_lt (lt_min hε₀ (lt_min (by norm_num) (sq_pos_of_pos ha)))) (pow_le_one₀ hα.1.le hα.2))
  have hbα : b ≤ α ^ 2 := hsmall.trans ((mul_le_of_le_one_left (pow_nonneg hα.1.le _) hε1).trans
    (pow_le_pow_of_le_one hα.1.le hα.2 (by omega : 2 ≤ 2 * J)))
  have hroot : Real.sqrt b ≤ a := Real.sqrt_le_iff.mpr
    ⟨ha.le, hbε.trans ((min_le_right _ _).trans (min_le_right _ _))⟩
  have HC : C * Real.sqrt b ≤ 1 / 4 := (mul_le_mul_of_nonneg_left hroot hC0.le).trans_eq (by dsimp only [a]; field_simp)
  have hsmall₀ := hsmall.trans (mul_le_mul_of_nonneg_right (min_le_left ε₀ (min 1 (a ^ 2))) (pow_nonneg hα.1.le _))
  obtain ⟨HV, Hf, _, _, Hr, Hw⟩ := HA η α b u w hηlo hηhi hα hb hsmall₀ hsum hu hw
  refine ⟨HV, Hf, HC, ?_⟩
  intro d hd0 hd1 hd2
  have H := terminal_phase_cone_direction (fderiv ℝ (terminalConnectionPhase h) Y) d hα.1
    (le_trans (by norm_num) hA) hb.le hbα hu.le hw.le
    (by simpa only [abs_of_pos hu, abs_of_pos hw] using hsum) hd0 hd1 hd2 Hr Hw
  change |α ^ 2 * fderiv ℝ (terminalConnectionPhase h) Y d + 1| ≤ C * Real.sqrt b at H
  have Hsign : α ^ 2 * fderiv ℝ (terminalConnectionPhase h) Y d ≤ -(3 / 4) := by
    linarith only [(abs_le.mp (H.trans HC)).2]
  have Hneg : fderiv ℝ (terminalConnectionPhase h) Y d < 0 := by
    nlinarith only [Hsign, sq_nonneg α]
  refine ⟨H, Hneg, ?_⟩
  rw [abs_of_neg Hneg]
  apply (div_le_iff₀ (mul_pos (by norm_num) (sq_pos_of_pos hα.1))).mpr
  nlinarith only [Hsign]

theorem exists_terminal_phase_cone_frozen_bounds :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → 2 * η ≤ δ →
      ∀ J : ℕ, 4 ≤ J → ∃ C ≥ (1 : ℝ), ∃ ε > (0 : ℝ), ∀ α₀ α b u w : ℝ,
      0 < α₀ → (0 < α ∧ α ≤ 1) → |Real.log (α / α₀)| < Real.log 2 / J →
      0 < b → b ≤ ε * α₀ ^ (2 * J + 1) → |u| + |w| ≤ b → 0 < u → 0 < w →
      let Y : ExitTailState := ![2 + 2 * α, u, w]
      let h := η * α₀ ^ J
      coreTailValid h Y ∧ ContDiffAt ℝ 2 (terminalConnectionPhase h) Y ∧
        C * Real.sqrt b ≤ 1 / 4 ∧ ∀ d : ExitTailState,
          d 0 = 1 → |d 1| ≤ Real.sqrt u → |d 2| ≤ Real.sqrt w →
          |α ^ 2 * fderiv ℝ (terminalConnectionPhase h) Y d + 1| ≤ C * Real.sqrt b ∧
          fderiv ℝ (terminalConnectionPhase h) Y d < 0 ∧
          3 / (4 * α ^ 2) ≤ |fderiv ℝ (terminalConnectionPhase h) Y d| := by
  obtain ⟨δ, hδ, hδhi, HE⟩ := exists_terminal_phase_cone_bounds
  refine ⟨δ, hδ, hδhi, ?_⟩
  intro η hη hηhi J hJ
  obtain ⟨C, hC, ε₀, hε₀, HC⟩ := HE (η / 2) ⟨by positivity, by linarith only [hη, hηhi]⟩ J hJ
  refine ⟨C, hC, ε₀ / 8, by positivity, ?_⟩
  intro α₀ α b u w hα₀ hα hband hb hsmall hsum hu hw Y h
  let ηeff := η * α₀ ^ J / α ^ J
  have hJ1 : 1 ≤ J := by omega
  have hηeff := terminal_frozen_height_coefficient hη hα.1 hα₀ hJ1 hband
  have hheight : ηeff * α ^ J = h := div_mul_cancel₀ _ (pow_ne_zero J hα.1.ne')
  have hratio := terminal_logBand_power_ratio hα.1 hα₀ hJ1 hband
  have hpower : α₀ ^ J ≤ 2 * α ^ J := by linarith only [hratio.1]
  have hamp := terminal_powerBand_amplitude_ratio hα.1 hα₀ hJ1 hpower
  have hsmall₀ : b ≤ ε₀ * α ^ (2 * J) := calc
    b ≤ (ε₀ / 8) * α₀ ^ (2 * J + 1) := hsmall
    _ ≤ (ε₀ / 8) * (8 * α ^ (2 * J + 1)) := mul_le_mul_of_nonneg_left hamp (by positivity)
    _ = ε₀ * α ^ (2 * J + 1) := by ring
    _ ≤ ε₀ * α ^ (2 * J) := mul_le_mul_of_nonneg_left
      (pow_le_pow_of_le_one hα.1.le hα.2 (by omega)) hε₀.le
  have H := HC ηeff α b u w hηeff.1.le (hηeff.2.le.trans hηhi) hα hb hsmall₀ hsum hu hw
  dsimp only at H
  rwa [hheight] at H

end BianchiIX
