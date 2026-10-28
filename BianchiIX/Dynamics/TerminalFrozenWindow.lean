import BianchiIX.Algebra.TerminalPhaseWindow
import BianchiIX.Dynamics.TerminalHeightInterval
import BianchiIX.Dynamics.ExitTailHeightDerivativeBounds

noncomputable section

namespace BianchiIX

/-- A proportional phase window supports fixed-height Taylor comparison, including signed and zero walls. -/
theorem exists_terminal_frozen_phase_window {εin η : ℝ}
    (hεin : 0 < εin ∧ εin ≤ 1 / 10000) (hη : 0 < η) (hηhi : 2 * η ≤ 1 / 100)
    {q J : ℕ} (hJ : q + 2 ≤ J) (hηin : 2 * η ≤ εin / (4 * (11 / 5) ^ q)) :
    ∃ C ≥ (1 : ℝ), ∃ ε > (0 : ℝ), ∀ α₀ α b u w : ℝ,
      0 < α₀ → (0 < α ∧ α ≤ 1) →
      |Real.log (α / α₀)| < Real.log 2 / J →
      0 < b → b ≤ ε * α₀ ^ (2 * J + 1) → |u| + |w| ≤ b →
      let Y : ExitTailState := ![2 + 2 * α, u, w]
      let h := η * α₀ ^ J
      let F := fun Z => toExitTailState (coreTailState h Z)
      coreTailValid h Y ∧ ContDiffAt ℝ 2 F Y ∧
        ‖fderiv ℝ F Y‖ ≤ C ∧ ‖fderiv ℝ (fderiv ℝ F) Y‖ ≤ C * exitTailLength η α₀ J ∧
        0 < projectiveCycleDenom (coreTailState h Y) ∧
        2 < projectiveCycle (coreTailState h Y) 0 ∧
        (|projectiveCycle (coreTailState h Y) 1| ≤ 1 / 400 ∧
          |projectiveCycle (coreTailState h Y) 3| ≤ 1 / 400) ∧
        ((0 < u ∧ 0 < w) →
          entranceReturnValid (projectiveCycle (coreTailState h Y)) ∧
          ContDiffAt ℝ 2 (terminalConnectionTime h) Y ∧
          ContDiffAt ℝ 2 (terminalConnectionState h) Y ∧
          terminalConnectionTime h Y = terminalConnectionTime (η * α ^ J) Y ∧
          terminalConnectionState h Y = terminalConnectionState (η * α ^ J) Y) := by
  have hηlo : 0 < η / 2 ∧ η / 2 ≤ 1 / 100 := ⟨by positivity, by linarith only [hη, hηhi]⟩
  have hηlo1 : η / 2 < 1 := by linarith only [hηlo.2]
  have hJ1 : 1 ≤ J := by omega
  obtain ⟨C, hC, εd, hεd, HD⟩ := exists_terminal_exitReturn_two_bounds_uniform ⟨hηlo.1, hηlo1⟩ hJ1
  obtain ⟨εc, hεc, HC⟩ := exists_terminal_connection_height_interval hεin hηlo hJ
  obtain ⟨Cz, _, εz, hεz, HZ⟩ := exists_terminal_axisCycle_endpoint_uniform hηlo (by omega : 2 ≤ J)
  let ε₀ := min εd (min εc εz)
  have hε₀ : 0 < ε₀ := lt_min hεd (lt_min hεc hεz)
  refine ⟨C, hC, ε₀ / 8, by positivity, ?_⟩
  intro α₀ α b u w hα₀ hα hband hb hsmall hsum Y h F
  have hαpos : 0 < α := hα.1
  let ηeff := η * α₀ ^ J / α ^ J
  have hbandη : η / 2 < ηeff ∧ ηeff < 2 * η :=
    terminal_frozen_height_coefficient hη hα.1 hα₀ hJ1 hband
  have hηeff : 0 < ηeff := hηlo.1.trans hbandη.1
  have hηeff100 : ηeff ≤ 1 / 100 := hbandη.2.le.trans hηhi
  have hηeff1 : ηeff < 1 := by linarith only [hηeff100]
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
  have hsmalld : b ≤ εd * α ^ J := hsmall₀.trans
    ((mul_le_mul_of_nonneg_right (min_le_left _ _) (pow_nonneg hα.1.le (2 * J))).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hα.1.le hα.2 (by omega)) hεd.le))
  have hsmallc : b ≤ εc * α ^ (2 * J) := hsmall₀.trans
    (mul_le_mul_of_nonneg_right ((min_le_right _ _).trans (min_le_left _ _)) (pow_nonneg hα.1.le (2 * J)))
  have hsmallz : b ≤ εz * α ^ (2 * J) := hsmall₀.trans
    (mul_le_mul_of_nonneg_right ((min_le_right _ _).trans (min_le_right _ _)) (pow_nonneg hα.1.le (2 * J)))
  have heS : exitTailLength ηeff α J = exitTailLength η α₀ J := by
    apply neg_injective
    apply Real.exp_injective
    rw [exp_neg_exitTailLength hηeff hα.1 J, exp_neg_exitTailLength hη hα₀ J]
    exact hheight
  have Hder := HD ηeff α b u w hbandη.1.le hηeff1 hα hb hsmalld hsum
  dsimp only at Hder
  rw [hheight, heS] at Hder
  have Hz := HZ ηeff α b u w hbandη.1.le hηeff100 hα hb hsmallz hsum
  dsimp only at Hz
  rw [hheight] at Hz
  have hlow : (19 / 10 : ℝ) ≤ 19 / (10 * α) := by
    apply (le_div_iff₀ (by positivity : 0 < 10 * α)).mpr
    linarith only [hα.2]
  refine ⟨Hder.1, Hder.2.1, Hder.2.2.1, Hder.2.2.2,
    lt_trans (by positivity) Hz.2.2.1.1, ?_, ?_, ?_⟩
  · linarith only [Hz.2.2.2.1.1, hlow]
  · have HU := Hz.2.2.2.2.2.1
    have HW := Hz.2.2.2.2.2.2.1.2
    have hCB := Hz.2.2.2.2.2.2.2.2.2
    have hCBsq : Cz * b ≤ α ^ 2 / 10000 := hCB.trans
      (div_le_div_of_nonneg_right (pow_le_pow_of_le_one hα.1.le hα.2 (by omega)) (by norm_num))
    have hUpos : 0 < projectiveCycle (coreTailState h Y) 1 :=
      lt_of_lt_of_le (mul_pos (div_pos hηeff (by norm_num)) (pow_pos hα.1 (J - 2))) HU.1
    have hUpow := mul_le_mul_of_nonneg_left (pow_le_one₀ hα.1.le hα.2 (n := J - 2))
      (by positivity : 0 ≤ 2 * ηeff)
    have hpowq : (1 : ℝ) ≤ (11 / 5) ^ q := one_le_pow₀ (by norm_num)
    have hηbudget := (le_div_iff₀ (by positivity : (0 : ℝ) < 4 * (11 / 5) ^ q)).mp
      (hbandη.2.le.trans hηin)
    refine ⟨?_, HW.trans ?_⟩
    · rw [abs_of_pos hUpos]
      nlinarith only [HU.2, hUpow, hηbudget, hεin.2,
        mul_le_mul_of_nonneg_left hpowq hηeff.le]
    · apply (div_le_iff₀ (sq_pos_of_pos hα.1)).mpr
      nlinarith only [hCBsq, sq_nonneg α]
  · intro hpos
    have Hf := HC ηeff α b u w hbandη.1.le hηeff100 (hbandη.2.le.trans hηin)
      hα hb hsmallc hsum hpos.1 hpos.2
    dsimp only at Hf
    rw [hheight] at Hf
    have Hn := HC η α b u w (by linarith only [hη]) (by linarith only [hηhi, hη])
      (by linarith only [hηin, hη]) hα hb hsmallc hsum hpos.1 hpos.2
    have htime := Hf.2.2.2.1.unique Hn.2.2.2.1
    have hfixed : ContDiffAt ℝ 2 (fun Z : CoreAngleState => (h, Z)) Y :=
      contDiffAt_const.prodMk contDiffAt_id
    refine ⟨Hf.2.1, ?_, ?_, htime, Hf.2.2.2.2.symm.trans ?_⟩
    · exact ContDiffAt.comp (g := fun p : ℝ × CoreAngleState => terminalConnectionTime p.1 p.2)
        (f := fun Z => (h, Z)) Y Hf.2.2.1.1 hfixed
    · exact ContDiffAt.comp (g := fun p : ℝ × CoreAngleState => terminalConnectionState p.1 p.2)
        (f := fun Z => (h, Z)) Y Hf.2.2.1.2.1 hfixed
    · rw [htime]
      exact Hn.2.2.2.2

end BianchiIX
