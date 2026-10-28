import BianchiIX.Dynamics.EntranceTerminalPhaseBounds
import BianchiIX.Dynamics.TerminalHeightInterval
import BianchiIX.Dynamics.TerminalEntranceDerivativeBounds

noncomputable section

namespace BianchiIX

/-- One entrance threshold supplies the actual phase columns uniformly in the terminal height. -/
theorem exists_terminal_phase_column_inputs :
    ∃ A ≥ (1 : ℝ), ∃ δ > (0 : ℝ), δ ≤ 1 / 1000 ∧ ∀ η₀ : ℝ,
      (0 < η₀ ∧ η₀ ≤ δ) → ∀ J : ℕ, 2 ≤ J →
      ∃ ε > (0 : ℝ), ∀ η α b u w : ℝ,
      η₀ ≤ η → η ≤ δ → (0 < α ∧ α ≤ 1) → 0 < b →
      b ≤ ε * α ^ (2 * J) → |u| + |w| ≤ b → 0 < u → 0 < w →
      let Y : ExitTailState := ![2 + 2 * α, u, w]
      let h := η * α ^ J
      let y := terminalCyclicInput h Y
      coreTailValid h Y ∧ 0 < projectiveCycleDenom (coreTailState h Y) ∧
        (0 < y 1 ∧ y 1 ≤ 1) ∧ (0 < y 2 ∧ y 2 < 1) ∧ (0 < y 3 ∧ y 3 ≤ 1) ∧ y 3 ≤ y 1 ∧
        ∃ Ψ : ProjectiveState → ProjectiveState, EntranceRadialInverseAt y Ψ ∧
        let z := terminalEntranceInput h Y
        let F := fun z => coreRadius (entranceReturnState (Ψ z) 0) (entranceReturnState (Ψ z) 2)
        ContDiffAt ℝ 2 F z ∧ |F z - z 0| ≤ A * α * y 1 * y 2 ∧
          |fderiv ℝ F z (Pi.single 0 1) - 1| ≤ A * y 1 * y 2 ∧
          |fderiv ℝ F z (Pi.single 1 1)| ≤ A * α * y 2 ∧
          |fderiv ℝ F z (Pi.single 2 1)| ≤ A * y 1 ∧
          |fderiv ℝ F z (Pi.single 3 1)| ≤ A * α * y 1 * y 2 := by
  obtain ⟨A, hA, δin, hδin, hδinhi, HA⟩ := exists_entrance_terminal_phase_bounds
  let δ := min (δin / 4) (1 / 1000)
  have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
  refine ⟨A, hA, δ, hδ, min_le_right _ _, ?_⟩
  intro η₀ hη₀ J hJ
  have hη₀pos : 0 < η₀ := hη₀.1
  have hη₀hi : η₀ ≤ 1 / 100 := (hη₀.2.trans (min_le_right _ _)).trans (by norm_num)
  obtain ⟨εi, hεi, HI⟩ := exists_terminal_cycle_entrance_inputs_uniform hδin ⟨hη₀.1, hη₀hi⟩
    (q := 0) (by omega : 0 + 2 ≤ J)
  obtain ⟨B, hB, εg, hεg, HG⟩ := exists_terminal_axisCycle_endpoint_uniform ⟨hη₀.1, hη₀hi⟩ hJ
  have hB0 : 0 < B := lt_of_lt_of_le (by norm_num) hB
  let ε := min εi (min εg (η₀ / (4 * B)))
  refine ⟨ε, lt_min hεi (lt_min hεg (by positivity)), ?_⟩
  intro η α b u w hηlo hηhi hα hb hsmall hsum hu hw Y h y
  have hα0 : 0 < α := hα.1
  have hη100 : η ≤ 1 / 100 := (hηhi.trans (min_le_right _ _)).trans (by norm_num)
  have hηin : η ≤ δin / (4 * (11 / 5) ^ (0 : ℕ)) := by
    simpa only [pow_zero, mul_one] using hηhi.trans (min_le_left _ _)
  have hsi := hsmall.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (pow_nonneg hα.1.le (2 * J)))
  have hsg := hsmall.trans (mul_le_mul_of_nonneg_right
    ((min_le_right _ _).trans (min_le_left _ _)) (pow_nonneg hα.1.le (2 * J)))
  obtain ⟨HV, _, HK, HM, HU, HVwall, HW, _, HH⟩ := HI η α b u w hηlo hη100 hηin hα hb hsi hsum hu hw
  obtain ⟨_, _, _, _, Hrad, HUscale, HWscale, _, _, _⟩ := HG η α b u w hηlo hη100 hα hb hsg hsum
  change 2 < y 0 at HM
  change 0 < y 2 ∧ y 2 < 1 / 2 at HVwall
  change 19 / (10 * α) < coreRadius (y 0) (y 2) ∧ coreRadius (y 0) (y 2) < 11 / (5 * α) at Hrad
  have hka : 1 / α ≤ coreRadius (y 0) (y 2) := le_trans (by
    apply (div_le_div_iff₀ hα.1 (by positivity : 0 < 10 * α)).mpr
    linarith only [hα.1]) Hrad.1.le
  have hbudget : B * b ≤ η₀ / 4 * α ^ (2 * J) := by
    have Hε := (le_div_iff₀ (mul_pos (by norm_num) hB0)).mp
      ((min_le_right εi (min εg (η₀ / (4 * B)))).trans (min_le_right _ _))
    nlinarith only [mul_le_mul_of_nonneg_left hsmall hB0.le,
      mul_le_mul_of_nonneg_right Hε (pow_nonneg hα.1.le (2 * J))]
  have Hweak : y 3 ≤ η₀ / 2 * α ^ (2 * J - 2) := by
    have H := (le_abs_self _).trans (HWscale.2.trans
      (exitCycle_scaled_wall_power hα.1 (by omega : 2 ≤ 2 * J) hbudget))
    change y 3 ≤ 2 * (η₀ / 4) * α ^ (2 * J - 2) at H
    convert H using 1
    ring
  have hwu : y 3 ≤ y 1 := Hweak.trans ((mul_le_mul
    (by linarith only [hηlo] : η₀ / 2 ≤ η / 2)
    (pow_le_pow_of_le_one hα.1.le hα.2 (by omega : J - 2 ≤ 2 * J - 2))
    (pow_nonneg hα.1.le (2 * J - 2)) (by linarith only [hη₀.1, hηlo] : 0 ≤ η / 2)).trans HUscale.1)
  have hV : 0 < y 2 ∧ y 2 < 1 := ⟨HVwall.1, by linarith only [HVwall.2]⟩
  have hin1 : δin ≤ 1 := hδinhi.trans (by norm_num)
  refine ⟨HV, HH, ⟨HU.1, HU.2.1.trans hin1⟩, hV, ⟨HW.1, HW.2.1.trans hin1⟩, hwu, ?_⟩
  exact HA α y hα hka HK.le (by linarith only [HM]) ⟨HU.1, HU.2.1⟩ hV ⟨HW.1, HW.2.1⟩ hwu

end BianchiIX
