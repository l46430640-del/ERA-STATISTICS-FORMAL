import BianchiIX.Dynamics.EntranceSingleValueComparison
import BianchiIX.Dynamics.TerminalSinglePhaseGerm
import BianchiIX.Dynamics.TerminalConnectionDifferential
import BianchiIX.Dynamics.TerminalHeightInterval
import BianchiIX.Dynamics.CoreTailMultipliers

noncomputable section

namespace BianchiIX

theorem terminalCyclicInput_wall_product {h : ℝ} {Y : ExitTailState} (HV : coreTailValid h Y) :
    let z := terminalCyclicInput h Y
    let S := coreTailState h Y 1 + coreTailState h Y 3
    z 1 * (z 2 + z 3) + (z 2 + z 3) ^ 2 =
      16 / projectiveCycleDenom (coreTailState h Y) ^ 2 * (h * S + S ^ 2) := by
  change (4 * coreTailState h Y 2 / _) * (4 * coreTailState h Y 3 / _ + 4 * coreTailState h Y 1 / _) +
    (4 * coreTailState h Y 3 / _ + 4 * coreTailState h Y 1 / _) ^ 2 = _
  rw [coreTailState_active HV]
  ring

/-- The comparison constant precedes every auxiliary height and initial condition. -/
theorem exists_terminal_single_value_comparison :
    ∃ C ≥ (1 : ℝ), ∀ (h : ℝ) (Y : ExitTailState), coreTailValid h Y →
      let z := terminalCyclicInput h Y
      7 / 4 ≤ coreRadius (z 0) (z 2) → 2 ≤ z 0 →
      (0 ≤ z 1 ∧ z 1 ≤ 1 / 10000) → (0 < z 2 ∧ z 2 < 1) →
      (0 ≤ z 3 ∧ z 3 ≤ 1 / 10000) →
      let S := coreTailState h Y 1 + coreTailState h Y 3
      |2 / terminalConnectionPhase h Y - terminalSinglePhase h Y| ≤
        C / projectiveCycleDenom (coreTailState h Y) ^ 2 * (h * S + S ^ 2) := by
  obtain ⟨C, hC, HC⟩ := exists_entrance_single_value_comparison
  refine ⟨16 * C, by linarith only [hC], ?_⟩
  intro h Y HV z hk hm hu hv hw S
  have H := HC z hk hm hu hv hw
  change |2 / terminalConnectionPhase h Y - terminalSinglePhase h Y| ≤ _ at H
  exact H.trans_eq (by rw [terminalCyclicInput_wall_product HV]; ring)

/-- On the actual terminal domain the comparison retains the vanishing height factor uniformly in height. -/
theorem exists_terminal_single_value_comparison_uniform :
    ∃ C ≥ (1 : ℝ), ∀ η₀ : ℝ, (0 < η₀ ∧ η₀ ≤ 1 / 40000) →
      ∀ J : ℕ, 2 ≤ J → ∃ ε > (0 : ℝ), ∀ η α b u w : ℝ,
      η₀ ≤ η → η ≤ 1 / 40000 → (0 < α ∧ α ≤ 1) →
      0 < b → b ≤ ε * α ^ (2 * J) → |u| + |w| ≤ b → 0 < u → 0 < w →
      let Y : ExitTailState := ![2 + 2 * α, u, w]
      let h := η * α ^ J
      let S := coreTailState h Y 1 + coreTailState h Y 3
      coreTailValid h Y ∧
        |2 / terminalConnectionPhase h Y - terminalSinglePhase h Y| ≤ C / α ^ 4 * (h * S + S ^ 2) := by
  obtain ⟨C, hC, HC⟩ := exists_terminal_single_value_comparison
  refine ⟨C, hC, ?_⟩
  intro η₀ hη₀ J hJ
  have hη₀' : 0 < η₀ ∧ η₀ ≤ 1 / 100 := ⟨hη₀.1, by linarith only [hη₀.2]⟩
  obtain ⟨εe, hεe, HE⟩ := exists_terminal_cycle_entrance_inputs_uniform
    (by norm_num : (0 : ℝ) < 1 / 10000) hη₀' (q := 0) (by omega : 0 + 2 ≤ J)
  obtain ⟨_, _, εg, hεg, HG⟩ := exists_terminal_axisCycle_endpoint_uniform hη₀' hJ
  refine ⟨min εe εg, lt_min hεe hεg, ?_⟩
  intro η α b u w hηlo hηhi hα hb hsmall hsum hu hw Y h S
  have hse := hsmall.trans (mul_le_mul_of_nonneg_right (min_le_left εe εg) (pow_nonneg hα.1.le _))
  have hsg := hsmall.trans (mul_le_mul_of_nonneg_right (min_le_right εe εg) (pow_nonneg hα.1.le _))
  have hη100 : η ≤ 1 / 100 := by linarith only [hηhi]
  obtain ⟨HV, _, HK, HM, HU, HVa, HW, _, _⟩ := HE η α b u w hηlo hη100
    (by norm_num; exact hηhi) hα hb hse hsum hu hw
  obtain ⟨_, _, HH, _⟩ := HG η α b u w hηlo hη100 hα hb hsg hsum
  have H := HC h Y HV HK.le HM.le ⟨HU.1.le, HU.2.1⟩
    ⟨HVa.1, HVa.2.trans (by norm_num : (1 / 2 : ℝ) < 1)⟩ ⟨HW.1.le, HW.2.1⟩
  have hS : 0 ≤ S := by
    have H0 := coreTailMultiplier_formula HV 0
    have H1 := coreTailMultiplier_formula HV 1
    change coreTailState h Y 1 = u * coreTailMultiplier h Y 0 at H0
    change coreTailState h Y 3 = w * coreTailMultiplier h Y 1 at H1
    dsimp only [S]
    rw [H0, H1]
    exact add_nonneg (mul_nonneg hu.le (coreTailMultiplier_pos h Y 0).le)
      (mul_nonneg hw.le (coreTailMultiplier_pos h Y 1).le)
  have hh : 0 ≤ h := mul_nonneg (hη₀.1.le.trans hηlo) (pow_nonneg hα.1.le _)
  have hH : α ^ 2 ≤ projectiveCycleDenom (coreTailState h Y) := by
    change 399 / 100 * α ^ 2 < projectiveCycleDenom (coreTailState h Y) ∧ _ at HH
    nlinarith only [HH.1, sq_nonneg α]
  have hHsq : α ^ 4 ≤ projectiveCycleDenom (coreTailState h Y) ^ 2 := by
    simpa only [← pow_mul] using pow_le_pow_left₀ (sq_nonneg α) hH 2
  refine ⟨HV, H.trans ?_⟩
  exact mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_left (by linarith only [hC] : 0 ≤ C) (pow_pos hα.1 4) hHsq)
    (add_nonneg (mul_nonneg hh hS) (sq_nonneg S))

end BianchiIX
