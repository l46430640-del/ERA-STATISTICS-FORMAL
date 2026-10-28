import BianchiIX.Dynamics.TerminalWallFactorBounds

noncomputable section

namespace BianchiIX

/-- The actual factors retain (D.25) throughout the proportional phase window at one fixed height. -/
theorem exists_terminalWallFactor_frozen_bounds {η : ℝ} (hη : 0 < η) (hηhi : 2 * η ≤ 1 / 100)
    {J : ℕ} (hJ : 2 ≤ J) :
    ∃ C ≥ (1 : ℝ), ∃ ε > (0 : ℝ), ∀ α₀ α b u w : ℝ,
      0 < α₀ → (0 < α ∧ α ≤ 1) → |Real.log (α / α₀)| < Real.log 2 / J →
      0 < b → b ≤ ε * α₀ ^ (2 * J + 1) → |u| + |w| ≤ b →
      let Y : ExitTailState := ![2 + 2 * α, u, w]
      let h := η * α₀ ^ J
      let z := terminalEntranceInput h Y
      coreTailValid h Y ∧ z 2 = w * terminalWallFactor h Y 1 ∧ z 3 = u * terminalWallFactor h Y 0 ∧
        (η / 4 * α ^ (J - 2) ≤ z 1 ∧ z 1 ≤ 4 * η * α ^ (J - 2)) ∧
        ‖fderiv ℝ (fun Z => Real.log (terminalEntranceInput h Z 1)) Y‖ ≤ C / α ∧
        ∀ i : Fin 2, 0 < terminalWallFactor h Y i ∧
          ContDiffAt ℝ 2 (fun Z => terminalWallFactor h Z i) Y ∧
          ContDiffAt ℝ 2 (fun Z => Real.log (terminalWallFactor h Z i)) Y ∧
          terminalWallFactor h Y i ≤ C / α ^ 2 ∧
          (terminalWallFactor h Y i)⁻¹ ≤ C * α ^ 2 ∧
          ‖fderiv ℝ (fun Z => Real.log (terminalWallFactor h Z i)) Y‖ ≤ C / α := by
  have hηlo : 0 < η / 2 ∧ η / 2 ≤ 1 / 100 := ⟨by positivity, by linarith only [hη, hηhi]⟩
  obtain ⟨C, hC, ε₀, hε₀, HE⟩ := exists_terminalWallFactor_bounds_uniform hηlo hJ
  refine ⟨C, hC, ε₀ / 8, by positivity, ?_⟩
  intro α₀ α b u w hα₀ hα hband hb hsmall hsum Y h z
  let ηeff := η * α₀ ^ J / α ^ J
  have hJ1 : 1 ≤ J := by omega
  have hηeff : η / 2 < ηeff ∧ ηeff < 2 * η :=
    terminal_frozen_height_coefficient hη hα.1 hα₀ hJ1 hband
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
  have H := HE ηeff α b u w hηeff.1.le (hηeff.2.le.trans hηhi) hα hb hsmall₀ hsum
  dsimp only at H
  rw [hheight] at H
  obtain ⟨HV, Hv, Hw, Hu, Hlog, HB⟩ := H
  refine ⟨HV, Hv, Hw, ⟨?_, ?_⟩, Hlog, HB⟩
  · exact (mul_le_mul_of_nonneg_right (by linarith only [hηeff.1] : η / 4 ≤ ηeff / 2)
      (pow_nonneg hα.1.le (J - 2))).trans Hu.1
  · exact Hu.2.trans (mul_le_mul_of_nonneg_right (by linarith only [hηeff.2] : 2 * ηeff ≤ 4 * η)
      (pow_nonneg hα.1.le (J - 2)))

end BianchiIX
