import BianchiIX.Dynamics.TerminalReciprocalErrorBounds

noncomputable section

namespace BianchiIX

/-- The powers in (D.30) come from the actual wall factors and hold uniformly in the auxiliary height. -/
theorem exists_terminal_reciprocal_error_power_bounds :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 1000 ∧ ∀ η₀ : ℝ, (0 < η₀ ∧ η₀ ≤ δ) →
      ∀ J : ℕ, 4 ≤ J → ∃ C ≥ (1 : ℝ), ∃ ε > (0 : ℝ), ∀ η α b u w : ℝ,
      η₀ ≤ η → η ≤ δ → (0 < α ∧ α ≤ 1) → 0 < b →
      b ≤ ε * α ^ (2 * J) → |u| + |w| ≤ b → 0 < u → 0 < w →
      let Y : ExitTailState := ![2 + 2 * α, u, w]
      let h := η * α ^ J
      coreTailValid h Y ∧ ContDiffAt ℝ 2 (terminalReciprocalError h) Y ∧
        1 / α ≤ terminalConnectionPhase h Y ∧ 1 / α ≤ terminalEntranceInput h Y 0 ∧
        |terminalReciprocalError h Y| ≤ C * w * α ^ (J - 1) ∧
        (|fderiv ℝ (terminalReciprocalError h) Y (Pi.single 0 1)| +
          |fderiv ℝ (terminalReciprocalError h) Y (Pi.single 1 1)| ≤ C * w * α ^ (J - 4)) ∧
        |fderiv ℝ (terminalReciprocalError h) Y (Pi.single 2 1)| ≤ C * α ^ (J - 2) := by
  obtain ⟨δ, hδ, hδhi, HE⟩ := exists_terminal_reciprocal_error_bounds
  refine ⟨δ, hδ, hδhi, ?_⟩
  intro η₀ hη₀ J hJ
  have hJ2 : 2 ≤ J := by omega
  obtain ⟨A, hA, εe, hεe, HA⟩ := HE η₀ hη₀ J hJ2
  have hη₀100 : 0 < η₀ ∧ η₀ ≤ 1 / 100 := ⟨hη₀.1, (hη₀.2.trans hδhi).trans (by norm_num)⟩
  obtain ⟨M, hM, εm, hεm, HM⟩ := exists_terminalWallFactor_bounds_uniform hη₀100 hJ2
  have hA0 : 0 ≤ A := le_trans (by norm_num) hA
  have hAM : A ≤ A * M := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hM hA0
  refine ⟨A * M, hA.trans hAM, min εe εm, lt_min hεe hεm, ?_⟩
  intro η α b u w hηlo hηhi hα hb hsmall hsum hu hw Y h
  have hη100 : η ≤ 1 / 100 := (hηhi.trans hδhi).trans (by norm_num)
  have hη2 : 2 * η ≤ 1 := by linarith only [hηhi.trans hδhi]
  have hα0 := hα.1
  have hse := hsmall.trans (mul_le_mul_of_nonneg_right (min_le_left εe εm) (pow_nonneg hα.1.le (2 * J)))
  have hsm := hsmall.trans (mul_le_mul_of_nonneg_right (min_le_right εe εm) (pow_nonneg hα.1.le (2 * J)))
  obtain ⟨HV, Hreg, HF, HR, H0, H01, H2⟩ := HA η α b u w hηlo hηhi hα hb hse hsum hu hw
  obtain ⟨_, Hfactor, _, HU, _, HB⟩ := HM η α b u w hηlo hη100 hα hb hsm hsum
  let z := terminalEntranceInput h Y
  change z 2 = w * terminalWallFactor h Y 1 at Hfactor
  change η / 2 * α ^ (J - 2) ≤ z 1 ∧ z 1 ≤ 2 * η * α ^ (J - 2) at HU
  have hU : z 1 ≤ α ^ (J - 2) := HU.2.trans (by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hη2 (pow_nonneg hα.1.le (J - 2)))
  have hV0 : 0 ≤ z 2 := by rw [Hfactor]; exact mul_nonneg hw.le (HB 1).1.le
  have hV : z 2 ≤ M * w / α ^ 2 := by
    rw [Hfactor]
    exact (mul_le_mul_of_nonneg_left (HB 1).2.2.2.1 hw.le).trans_eq (by ring)
  have hp4 : α ^ (J - 2) = α ^ (J - 4) * α ^ 2 := by
    rw [← pow_add]
    congr 1
    omega
  have hprod : z 1 * z 2 ≤ M * w * α ^ (J - 4) := by
    calc
      _ ≤ α ^ (J - 2) * (M * w / α ^ 2) := mul_le_mul hU hV hV0 (pow_nonneg hα.1.le (J - 2))
      _ = _ := by rw [hp4]; field_simp [hα.1.ne']
  have hp1 : α ^ (J - 4) * α ^ 3 = α ^ (J - 1) := by
    rw [← pow_add]
    congr 1
    omega
  refine ⟨HV, Hreg, HF, HR, ?_, ?_, ?_⟩
  · calc
      _ ≤ A * α ^ 3 * z 1 * z 2 := H0
      _ = (A * α ^ 3) * (z 1 * z 2) := by ring
      _ ≤ (A * α ^ 3) * (M * w * α ^ (J - 4)) :=
        mul_le_mul_of_nonneg_left hprod (by positivity)
      _ = (A * M) * w * (α ^ (J - 4) * α ^ 3) := by ring
      _ = _ := by rw [hp1]
  · calc
      _ ≤ A * z 1 * z 2 := H01
      _ = A * (z 1 * z 2) := by ring
      _ ≤ A * (M * w * α ^ (J - 4)) := mul_le_mul_of_nonneg_left hprod hA0
      _ = _ := by ring
  · exact H2.trans ((mul_le_mul_of_nonneg_left hU hA0).trans
      (mul_le_mul_of_nonneg_right hAM (pow_nonneg hα.1.le (J - 2))))

/-- The reciprocal bounds remain valid on the proportional phase neighborhood at one fixed height. -/
theorem exists_terminal_reciprocal_error_frozen_bounds :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 1000 ∧ ∀ η : ℝ, 0 < η → 2 * η ≤ δ →
      ∀ J : ℕ, 4 ≤ J → ∃ C ≥ (1 : ℝ), ∃ ε > (0 : ℝ), ∀ α₀ α b u w : ℝ,
      0 < α₀ → (0 < α ∧ α ≤ 1) → |Real.log (α / α₀)| < Real.log 2 / J →
      0 < b → b ≤ ε * α₀ ^ (2 * J + 1) → |u| + |w| ≤ b → 0 < u → 0 < w →
      let Y : ExitTailState := ![2 + 2 * α, u, w]
      let h := η * α₀ ^ J
      coreTailValid h Y ∧ ContDiffAt ℝ 2 (terminalReciprocalError h) Y ∧
        1 / α ≤ terminalConnectionPhase h Y ∧ 1 / α ≤ terminalEntranceInput h Y 0 ∧
        |terminalReciprocalError h Y| ≤ C * w * α ^ (J - 1) ∧
        (|fderiv ℝ (terminalReciprocalError h) Y (Pi.single 0 1)| +
          |fderiv ℝ (terminalReciprocalError h) Y (Pi.single 1 1)| ≤ C * w * α ^ (J - 4)) ∧
        |fderiv ℝ (terminalReciprocalError h) Y (Pi.single 2 1)| ≤ C * α ^ (J - 2) := by
  obtain ⟨δ, hδ, hδhi, HE⟩ := exists_terminal_reciprocal_error_power_bounds
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
