import BianchiIX.Dynamics.TerminalSingleCorrectionPowers
import BianchiIX.Dynamics.TerminalReciprocalErrorPowers

noncomputable section

namespace BianchiIX

def terminalBoundedPhaseError (h : ℝ) (Y : ExitTailState) : ℝ :=
  2 / terminalConnectionPhase h Y -
    singleStrongPhase (terminalCyclicInput h Y 0) (terminalCyclicInput h Y 1)

theorem terminalBoundedPhaseError_decomposition (h : ℝ) :
    terminalBoundedPhaseError h = fun Y => terminalSingleReciprocalError h Y + terminalReciprocalError h Y := by
  funext Y
  dsimp [terminalBoundedPhaseError, terminalSingleReciprocalError, terminalReciprocalError]
  ring

/-- All corrections between the single-wall phase and the exact arrival phase are O(b), including the ordinary radial derivative. -/
theorem exists_terminal_bounded_phase_error_bound :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η₀ : ℝ, (0 < η₀ ∧ η₀ ≤ δ) →
      ∀ J : ℕ, 4 ≤ J → ∃ C ≥ (1 : ℝ), ∃ ε > (0 : ℝ), ∀ η α b u w : ℝ,
      η₀ ≤ η → η ≤ δ → (0 < α ∧ α ≤ 1) →
      0 < b → b ≤ ε * α ^ (2 * J) → |u| + |w| ≤ b → 0 < u → 0 < w →
      let Y : ExitTailState := ![2 + 2 * α, u, w]
      let h := η * α ^ J
      coreTailValid h Y ∧ ContDiffAt ℝ 2 (terminalBoundedPhaseError h) Y ∧
        |terminalBoundedPhaseError h Y| +
          |fderiv ℝ (terminalBoundedPhaseError h) Y (Pi.single 0 1)| ≤ C * b := by
  obtain ⟨δ₀, hδ₀, hδ₀hi, HΨ⟩ := exists_terminal_reciprocal_error_power_bounds
  let δ := min δ₀ (1 / 40000)
  refine ⟨δ, lt_min hδ₀ (by norm_num), min_le_right _ _, ?_⟩
  intro η₀ hη₀ J hJ
  have hη₀' : 0 < η₀ ∧ η₀ ≤ 1 / 40000 := ⟨hη₀.1, hη₀.2.trans (min_le_right _ _)⟩
  obtain ⟨A, hA, εa, hεa, HA⟩ := exists_terminal_single_reciprocal_linear_bound hη₀' (by omega : 2 ≤ J)
  obtain ⟨B, hB, εb, hεb, HB⟩ := HΨ η₀ ⟨hη₀.1, hη₀.2.trans (min_le_left _ _)⟩ J hJ
  have hB0 : 0 ≤ B := (by norm_num : (0 : ℝ) ≤ 1).trans hB
  refine ⟨A + 2 * B, by linarith only [hA, hB], min εa εb, lt_min hεa hεb, ?_⟩
  intro η α b u w hηlo hηhi hα hb hsmall hsum hu hw Y h
  have hsa := hsmall.trans (mul_le_mul_of_nonneg_right (min_le_left εa εb) (pow_nonneg hα.1.le _))
  have hsb := hsmall.trans (mul_le_mul_of_nonneg_right (min_le_right εa εb) (pow_nonneg hα.1.le _))
  obtain ⟨HV, Ha, Hqa⟩ := HA η α b u w hηlo (hηhi.trans (min_le_right _ _)) hα hb hsa hsum
  obtain ⟨_, Hb, _, _, H0, H01, _⟩ := HB η α b u w hηlo (hηhi.trans (min_le_left _ _)) hα hb hsb hsum hu hw
  have hwB : w ≤ b := by linarith only [hsum, le_abs_self w, abs_nonneg u]
  have Hpow (n : ℕ) : B * w * α ^ n ≤ B * b :=
    (mul_le_of_le_one_right (mul_nonneg hB0 hw.le) (pow_le_one₀ hα.1.le hα.2)).trans
      (mul_le_mul_of_nonneg_left hwB hB0)
  have Hval : |terminalReciprocalError h Y| ≤ B * b := H0.trans (Hpow _)
  have Hder : |fderiv ℝ (terminalReciprocalError h) Y (Pi.single 0 1)| ≤ B * b :=
    (le_add_of_nonneg_right (abs_nonneg _)).trans (H01.trans (Hpow _))
  have Hreg := Ha.add Hb
  rw [← terminalBoundedPhaseError_decomposition h] at Hreg
  have HD := (Ha.differentiableAt (by norm_num)).hasFDerivAt.add (Hb.differentiableAt (by norm_num)).hasFDerivAt
  change HasFDerivAt (fun Z => terminalSingleReciprocalError h Z + terminalReciprocalError h Z) _ Y at HD
  rw [← terminalBoundedPhaseError_decomposition h] at HD
  refine ⟨HV, Hreg, ?_⟩
  rw [HD.fderiv, add_apply, terminalBoundedPhaseError_decomposition h]
  have H1 := abs_add_le (terminalSingleReciprocalError h Y) (terminalReciprocalError h Y)
  have H2 := abs_add_le (fderiv ℝ (terminalSingleReciprocalError h) Y (Pi.single 0 1))
    (fderiv ℝ (terminalReciprocalError h) Y (Pi.single 0 1))
  linarith only [H1, H2, Hqa, Hval, Hder]

theorem exists_terminal_bounded_phase_error_frozen_bound :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → 2 * η ≤ δ →
      ∀ J : ℕ, 4 ≤ J → ∃ C ≥ (1 : ℝ), ∃ ε > (0 : ℝ), ∀ α₀ α b u w : ℝ,
      0 < α₀ → (0 < α ∧ α ≤ 1) → |Real.log (α / α₀)| < Real.log 2 / J →
      0 < b → b ≤ ε * α₀ ^ (2 * J + 1) → |u| + |w| ≤ b → 0 < u → 0 < w →
      let Y : ExitTailState := ![2 + 2 * α, u, w]
      let h := η * α₀ ^ J
      coreTailValid h Y ∧ ContDiffAt ℝ 2 (terminalBoundedPhaseError h) Y ∧
        |terminalBoundedPhaseError h Y| +
          |fderiv ℝ (terminalBoundedPhaseError h) Y (Pi.single 0 1)| ≤ C * b := by
  obtain ⟨δ, hδ, hδhi, HE⟩ := exists_terminal_bounded_phase_error_bound
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
