import BianchiIX.Dynamics.TerminalBoundedPhaseStatistics
import BianchiIX.Analysis.ReciprocalPhaseStatistics

noncomputable section

namespace BianchiIX

theorem terminalConnectionPhase_two_div_bounded (h : ℝ) :
    terminalConnectionPhase h = fun Y => 2 / terminalBoundedPhase h Y := by
  funext Y
  simp only [terminalBoundedPhase, div_div_cancel₀ (by norm_num : (2 : ℝ) ≠ 0)]

theorem terminalConnectionPhase_relative_radial_identity {h α : ℝ} {Y : ExitTailState}
    (hα : α ≠ 0) (hx : terminalBoundedPhase h Y ≠ 0)
    (hf : ContDiffAt ℝ 2 (terminalBoundedPhase h) Y) :
    let δ := terminalBoundedPhase h Y - α;
    let e := 2 * fderiv ℝ (terminalBoundedPhase h) Y (Pi.single 0 1) - 1;
    -α ^ 2 * fderiv ℝ (terminalConnectionPhase h) Y (Pi.single 0 1) =
        (1 + e) / (1 + δ / α) ^ 2 ∧
      (1 + e) / (1 + δ / α) ^ 2 - 1 =
        (e - 2 * (δ / α) - (δ / α) ^ 2) / (1 + δ / α) ^ 2 := by
  dsimp only
  rw [terminalConnectionPhase_two_div_bounded h,
    two_div_fderiv (hf.differentiableAt (by norm_num)) hx]
  exact reciprocal_phase_relative_identity hα hx

/-- The value and ordinary derivative estimates of (D.33) for the exact terminal arrival phase. -/
theorem exists_terminal_phase_statistics :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η₀ : ℝ, (0 < η₀ ∧ η₀ ≤ δ) →
      ∀ J : ℕ, 4 ≤ J → ∃ C ≥ (1 : ℝ), ∃ ε > (0 : ℝ), ∀ η α b u w : ℝ,
      η₀ ≤ η → η ≤ δ → (0 < α ∧ α ≤ 1) →
      0 < b → b ≤ ε * α ^ (2 * J) → |u| + |w| ≤ b → 0 < u → 0 < w →
      let Y : ExitTailState := ![2 + 2 * α, u, w]
      let h := η * α ^ J
      coreTailValid h Y ∧ ContDiffAt ℝ 2 (terminalConnectionPhase h) Y ∧
        0 < terminalConnectionPhase h Y ∧
        |terminalConnectionPhase h Y - 2 / α| ≤ C * b / α ^ 2 ∧
        |fderiv ℝ (terminalConnectionPhase h) Y (Pi.single 0 1) + 1 / α ^ 2| ≤ C * b / α ^ 3 ∧
        (|fderiv ℝ (terminalConnectionPhase h) Y (Pi.single 1 1)| +
          |fderiv ℝ (terminalConnectionPhase h) Y (Pi.single 2 1)| ≤ C / α ^ 2) := by
  obtain ⟨δ, hδ, hδhi, HE⟩ := exists_terminal_bounded_phase_statistics
  refine ⟨δ, hδ, hδhi, ?_⟩
  intro η₀ hη₀ J hJ
  obtain ⟨A, hA, ε₀, hε₀, HA⟩ := HE η₀ hη₀ J hJ
  have hA0 : 0 < A := lt_of_lt_of_le (by norm_num) hA
  refine ⟨20 * A, by linarith only [hA], min ε₀ (1 / (4 * A)),
    lt_min hε₀ (by positivity), ?_⟩
  intro η α b u w hηlo hηhi hα hb hsmall hsum hu hw Y h
  have hsmall₀ : b ≤ ε₀ * α ^ (2 * J) := hsmall.trans
    (mul_le_mul_of_nonneg_right (min_le_left _ _) (pow_nonneg hα.1.le _))
  have hbα : b ≤ (1 / (4 * A)) * α := hsmall.trans
    ((mul_le_mul_of_nonneg_right (min_le_right _ _) (pow_nonneg hα.1.le _)).trans
      (mul_le_mul_of_nonneg_left
        (by simpa only [pow_one] using pow_le_pow_of_le_one hα.1.le hα.2 (by omega : 1 ≤ 2 * J))
        (by positivity)))
  have hAb : A * b ≤ α / 4 := (mul_le_mul_of_nonneg_left hbα hA0.le).trans_eq (by field_simp)
  obtain ⟨HV, Hf, Herr, Hwall⟩ := HA η α b u w hηlo hηhi hα hb hsmall₀ hsum hu hw
  obtain ⟨hx, Hk, Hv, Hr, Hw⟩ := reciprocal_phase_statistics Hf hα hA0.le hb.le hAb Herr Hwall
  rw [← terminalConnectionPhase_two_div_bounded h] at Hk Hr Hw
  change |(fun Z => 2 / terminalBoundedPhase h Z) Y - 2 / α| ≤ _ at Hv
  rw [← terminalConnectionPhase_two_div_bounded h] at Hv
  refine ⟨HV, Hk, ?_, ?_, Hr, ?_⟩
  · rw [terminalConnectionPhase_two_div_bounded h]
    exact div_pos (by norm_num) hx
  · exact Hv.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
      (by linarith only [hA] : 4 * A ≤ 20 * A) hb.le) (sq_nonneg α))
  · exact Hw.trans (div_le_div_of_nonneg_right (by linarith only [hA] : 8 * A ≤ 20 * A) (sq_nonneg α))

theorem exists_terminal_phase_statistics_frozen :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → 2 * η ≤ δ →
      ∀ J : ℕ, 4 ≤ J → ∃ C ≥ (1 : ℝ), ∃ ε > (0 : ℝ), ∀ α₀ α b u w : ℝ,
      0 < α₀ → (0 < α ∧ α ≤ 1) → |Real.log (α / α₀)| < Real.log 2 / J →
      0 < b → b ≤ ε * α₀ ^ (2 * J + 1) → |u| + |w| ≤ b → 0 < u → 0 < w →
      let Y : ExitTailState := ![2 + 2 * α, u, w]
      let h := η * α₀ ^ J
      coreTailValid h Y ∧ ContDiffAt ℝ 2 (terminalConnectionPhase h) Y ∧
        0 < terminalConnectionPhase h Y ∧
        |terminalConnectionPhase h Y - 2 / α| ≤ C * b / α ^ 2 ∧
        |fderiv ℝ (terminalConnectionPhase h) Y (Pi.single 0 1) + 1 / α ^ 2| ≤ C * b / α ^ 3 ∧
        (|fderiv ℝ (terminalConnectionPhase h) Y (Pi.single 1 1)| +
          |fderiv ℝ (terminalConnectionPhase h) Y (Pi.single 2 1)| ≤ C / α ^ 2) := by
  obtain ⟨δ, hδ, hδhi, HE⟩ := exists_terminal_phase_statistics
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
