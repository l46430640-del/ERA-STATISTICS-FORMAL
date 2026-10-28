import BianchiIX.Dynamics.TerminalSinglePhaseComposition
import BianchiIX.Dynamics.TerminalBoundedPhaseCorrection
import BianchiIX.Analysis.ReciprocalCoordinateBound

noncomputable section

namespace BianchiIX

def terminalBoundedPhase (h : ℝ) (Y : ExitTailState) : ℝ := 2 / terminalConnectionPhase h Y

theorem terminalBoundedPhase_decomposition (h : ℝ) :
    terminalBoundedPhase h = fun Y => terminalSinglePhase h Y + terminalBoundedPhaseError h Y := by
  funext Y
  dsimp [terminalBoundedPhase, terminalSinglePhase, terminalBoundedPhaseError]
  ring

theorem terminalBoundedPhase_reciprocal_decomposition (h : ℝ) :
    terminalBoundedPhase h = fun Y => 2 / terminalEntranceInput h Y 0 + terminalReciprocalError h Y := by
  funext Y
  dsimp [terminalBoundedPhase, terminalReciprocalError]
  ring

/-- All estimates of (D.31) concern the actual arrival map at fixed auxiliary height. -/
theorem exists_terminal_bounded_phase_statistics :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η₀ : ℝ, (0 < η₀ ∧ η₀ ≤ δ) →
      ∀ J : ℕ, 4 ≤ J → ∃ C ≥ (1 : ℝ), ∃ ε > (0 : ℝ), ∀ η α b u w : ℝ,
      η₀ ≤ η → η ≤ δ → (0 < α ∧ α ≤ 1) →
      0 < b → b ≤ ε * α ^ (2 * J) → |u| + |w| ≤ b → 0 < u → 0 < w →
      let Y : ExitTailState := ![2 + 2 * α, u, w]
      let h := η * α ^ J
      coreTailValid h Y ∧ ContDiffAt ℝ 2 (terminalBoundedPhase h) Y ∧
        (|terminalBoundedPhase h Y - α| + |fderiv ℝ (terminalBoundedPhase h) Y (Pi.single 0 1) - 1 / 2| ≤ C * b) ∧
        (|fderiv ℝ (terminalBoundedPhase h) Y (Pi.single 1 1)| +
          |fderiv ℝ (terminalBoundedPhase h) Y (Pi.single 2 1)| ≤ C) := by
  obtain ⟨δc, hδc, hδchi, HC⟩ := exists_terminal_bounded_phase_error_bound
  obtain ⟨δp, hδp, _, HP⟩ := exists_terminal_reciprocal_error_power_bounds
  let δ := min δc δp
  have hδhi : δ ≤ 1 / 40000 := (min_le_left _ _).trans hδchi
  refine ⟨δ, lt_min hδc hδp, hδhi, ?_⟩
  intro η₀ hη₀ J hJ
  have hJ2 : 2 ≤ J := by omega
  have hη100 : 0 < η₀ ∧ η₀ ≤ 1 / 100 := ⟨hη₀.1, (hη₀.2.trans hδhi).trans (by norm_num)⟩
  have hη1000 : 0 < η₀ ∧ η₀ ≤ 1 / 1000 := ⟨hη₀.1, (hη₀.2.trans hδhi).trans (by norm_num)⟩
  obtain ⟨A, hA, εa, hεa, HA⟩ := exists_terminal_single_phase_composed_bounds hη100 hJ2
  obtain ⟨B, hB, εb, hεb, HB⟩ := HC η₀ ⟨hη₀.1, hη₀.2.trans (min_le_left _ _)⟩ J hJ
  obtain ⟨P, hP, εp, hεp, HΨ⟩ := HP η₀ ⟨hη₀.1, hη₀.2.trans (min_le_right _ _)⟩ J hJ
  obtain ⟨D, hD, εd, hεd, HD⟩ := exists_terminalEntranceInput_derivative_uniform hη1000 hJ2
  have hP0 : 0 ≤ P := (by norm_num : (0 : ℝ) ≤ 1).trans hP
  have hD0 : 0 ≤ D := (by norm_num : (0 : ℝ) ≤ 1).trans hD
  let C := A + B + 4 * D + 2 * P
  let ε := min εa (min εb (min εp (min εd 1)))
  refine ⟨C, by dsimp only [C]; linarith only [hA, hB, hD, hP],
    ε, lt_min hεa (lt_min hεb (lt_min hεp (lt_min hεd (by norm_num)))), ?_⟩
  intro η α b u w hηlo hηhi hα hb hsmall hsum hu hw Y h
  have hs (a : ℝ) (ha : ε ≤ a) : b ≤ a * α ^ (2 * J) :=
    hsmall.trans (mul_le_mul_of_nonneg_right ha (pow_nonneg hα.1.le _))
  have hsa := hs εa (min_le_left _ _)
  have hsb := hs εb ((min_le_right _ _).trans (min_le_left _ _))
  have hsp := hs εp ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hsd := hs εd ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hε1 : ε ≤ 1 := (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hb1 : b ≤ 1 := hsmall.trans ((mul_le_of_le_one_left (pow_nonneg hα.1.le _) hε1).trans
    (pow_le_one₀ hα.1.le hα.2))
  have hηsmall := hηhi.trans hδhi
  obtain ⟨HV, Hsa, Hs, _⟩ := HA η α b u w hηlo (hηsmall.trans (by norm_num)) hα hb hsa hsum
  obtain ⟨_, Hsb, He⟩ := HB η α b u w hηlo (hηhi.trans (min_le_left _ _)) hα hb hsb hsum hu hw
  obtain ⟨_, Hp, _, Hr, _, Hp01, Hp2⟩ := HΨ η α b u w hηlo (hηhi.trans (min_le_right _ _)) hα hb hsp hsum hu hw
  obtain ⟨_, _, Hi, _, Hdi, _⟩ := HD η α b u w hηlo (hηsmall.trans (by norm_num)) hα hb hsd hsum
  have Hsmooth := Hsa.add Hsb
  rw [← terminalBoundedPhase_decomposition h] at Hsmooth
  have HDS := (Hsa.differentiableAt (by norm_num)).hasFDerivAt.add (Hsb.differentiableAt (by norm_num)).hasFDerivAt
  change HasFDerivAt (fun Z => terminalSinglePhase h Z + terminalBoundedPhaseError h Z) _ Y at HDS
  rw [← terminalBoundedPhase_decomposition h] at HDS
  refine ⟨HV, Hsmooth, ?_, ?_⟩
  · have HVeq : terminalBoundedPhase h Y - α = (terminalSinglePhase h Y - α) + terminalBoundedPhaseError h Y := by
      rw [terminalBoundedPhase_decomposition h]; ring
    have HDeq : fderiv ℝ (terminalBoundedPhase h) Y (Pi.single 0 1) - 1 / 2 =
        (fderiv ℝ (terminalSinglePhase h) Y (Pi.single 0 1) - 1 / 2) +
          fderiv ℝ (terminalBoundedPhaseError h) Y (Pi.single 0 1) := by rw [HDS.fderiv, add_apply]; ring
    rw [HVeq, HDeq]
    have H1 := abs_add_le (terminalSinglePhase h Y - α) (terminalBoundedPhaseError h Y)
    have H2 := abs_add_le (fderiv ℝ (terminalSinglePhase h) Y (Pi.single 0 1) - 1 / 2)
      (fderiv ℝ (terminalBoundedPhaseError h) Y (Pi.single 0 1))
    dsimp only [C]
    nlinarith only [H1, H2, Hs, He, (by positivity : 0 ≤ (4 * D + 2 * P) * b)]
  · have Hinv := reciprocal_coordinate_differential_bound 0 Hi hα.1 hD0 Hr Hdi
    have HDR := (Hinv.1.differentiableAt (by norm_num)).hasFDerivAt.add (Hp.differentiableAt (by norm_num)).hasFDerivAt
    change HasFDerivAt (fun Z => 2 / terminalEntranceInput h Z 0 + terminalReciprocalError h Z) _ Y at HDR
    rw [← terminalBoundedPhase_reciprocal_decomposition h] at HDR
    have Hiv (i : Fin 3) : |fderiv ℝ (fun Z => 2 / terminalEntranceInput h Z 0) Y (Pi.single i 1)| ≤ 2 * D := by
      simpa only [Pi.norm_single, norm_one, mul_one] using Hinv.2 (Pi.single i 1)
    have hw1 : w ≤ 1 := by linarith only [hsum, hb1, le_abs_self w, abs_nonneg u]
    have HPw : P * w * α ^ (J - 4) ≤ P :=
      (mul_le_of_le_one_right (mul_nonneg hP0 hw.le) (pow_le_one₀ hα.1.le hα.2)).trans
        (mul_le_of_le_one_right hP0 hw1)
    have Hp1 : |fderiv ℝ (terminalReciprocalError h) Y (Pi.single 1 1)| ≤ P :=
      (le_add_of_nonneg_left (abs_nonneg _)).trans (Hp01.trans HPw)
    have Hp2' : |fderiv ℝ (terminalReciprocalError h) Y (Pi.single 2 1)| ≤ P :=
      Hp2.trans (mul_le_of_le_one_right hP0 (pow_le_one₀ hα.1.le hα.2))
    rw [HDR.fderiv, add_apply, add_apply]
    have H1 := abs_add_le (fderiv ℝ (fun Z => 2 / terminalEntranceInput h Z 0) Y (Pi.single 1 1))
      (fderiv ℝ (terminalReciprocalError h) Y (Pi.single 1 1))
    have H2 := abs_add_le (fderiv ℝ (fun Z => 2 / terminalEntranceInput h Z 0) Y (Pi.single 2 1))
      (fderiv ℝ (terminalReciprocalError h) Y (Pi.single 2 1))
    dsimp only [C]
    linarith only [H1, H2, Hiv 1, Hiv 2, Hp1, Hp2', hA, hB]

/-- The full bounded-phase statistics hold throughout the proportional neighborhood at one frozen height. -/
theorem exists_terminal_bounded_phase_statistics_frozen :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → 2 * η ≤ δ →
      ∀ J : ℕ, 4 ≤ J → ∃ C ≥ (1 : ℝ), ∃ ε > (0 : ℝ), ∀ α₀ α b u w : ℝ,
      0 < α₀ → (0 < α ∧ α ≤ 1) → |Real.log (α / α₀)| < Real.log 2 / J →
      0 < b → b ≤ ε * α₀ ^ (2 * J + 1) → |u| + |w| ≤ b → 0 < u → 0 < w →
      let Y : ExitTailState := ![2 + 2 * α, u, w]
      let h := η * α₀ ^ J
      coreTailValid h Y ∧ ContDiffAt ℝ 2 (terminalBoundedPhase h) Y ∧
        (|terminalBoundedPhase h Y - α| + |fderiv ℝ (terminalBoundedPhase h) Y (Pi.single 0 1) - 1 / 2| ≤ C * b) ∧
        (|fderiv ℝ (terminalBoundedPhase h) Y (Pi.single 1 1)| +
          |fderiv ℝ (terminalBoundedPhase h) Y (Pi.single 2 1)| ≤ C) := by
  obtain ⟨δ, hδ, hδhi, HE⟩ := exists_terminal_bounded_phase_statistics
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
