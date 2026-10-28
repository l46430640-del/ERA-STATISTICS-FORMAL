import BianchiIX.Dynamics.TerminalPhaseCone
import BianchiIX.Analysis.GraphPhaseInverse

noncomputable section

namespace BianchiIX

open Filter
open scoped Topology

def terminalNaturalPhase (η : ℝ) (J : ℕ) (Y : ExitTailState) : ℝ :=
  terminalConnectionPhase (η * ((Y 0 - 2) / 2) ^ J) Y

/-- Formula (D.22) for actual C1 entrance graphs, with the natural height and a genuine local inverse. -/
theorem exists_terminal_graph_inverse :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 4 ≤ J → ∃ C ≥ (1 : ℝ), ∃ ε > (0 : ℝ),
      ∀ (α b : ℝ) (U W : ℝ → ℝ), (0 < α ∧ α ≤ 1) →
      0 < b → b ≤ ε * α ^ (2 * J) →
      let r := 2 + 2 * α;
      0 < U r → 0 < W r → |U r| + |W r| ≤ b →
      ContDiffAt ℝ 1 U r → ContDiffAt ℝ 1 W r →
      |deriv U r| ≤ Real.sqrt (U r) → |deriv W r| ≤ Real.sqrt (W r) →
      let φ := graphPhase (terminalNaturalPhase η J) U W;
      coreTailValid (η * α ^ J) ![r, U r, W r] ∧
        ContDiffAt ℝ 1 φ r ∧ deriv φ r < 0 ∧
        ∃ g, ScalarLocalInverseAt φ r g ∧
          |Real.log (|deriv φ r| / (1 / α ^ 2))| +
            |Real.log (|deriv g (φ r)| / α ^ 2)| ≤ C * Real.sqrt b := by
  obtain ⟨δ, hδ, hδhi, HE⟩ := exists_terminal_phase_cone_bounds
  refine ⟨δ, hδ, hδhi, ?_⟩
  intro η hη hηhi J hJ
  obtain ⟨A, hA, εc, hεc, HC⟩ := HE η ⟨hη, hηhi⟩ J hJ
  have hη100 : η ≤ 1 / 100 := (hηhi.trans hδhi).trans (by norm_num)
  have hbudget : η ≤ (1 / 10000 : ℝ) / (4 * (11 / 5) ^ (0 : ℕ)) := by
    norm_num
    exact hηhi.trans hδhi
  obtain ⟨εh, hεh, HH⟩ := exists_terminal_connection_height_freezing
    (εin := 1 / 10000) (η := η) (q := 0) (J := J)
    (by norm_num) ⟨hη, hη100⟩ (by omega) hbudget
  refine ⟨4 * A, by linarith only [hA], min εc εh, lt_min hεc hεh, ?_⟩
  intro α b U W hα hb hsmall r hu hw hsum hU hW hUd hWd φ
  let Y : ExitTailState := ![r, U r, W r]
  let h := η * α ^ J
  have hsc := hsmall.trans (mul_le_mul_of_nonneg_right (min_le_left εc εh) (pow_nonneg hα.1.le _))
  have hsh := hsmall.trans (mul_le_mul_of_nonneg_right (min_le_right εc εh) (pow_nonneg hα.1.le _))
  obtain ⟨HV, Hf, Hsmall, Hcone⟩ := HC η α b (U r) (W r) le_rfl hηhi hα hb hsc hsum hu hw
  obtain ⟨_, _, Hfreeze⟩ := HH α b (U r) (W r) hα hb hsh hsum hu hw
  let a := fun Z : ExitTailState => η * ((Z 0 - 2) / 2) ^ J
  have ha : ContinuousAt a Y :=
    ((((continuousAt_apply 0 Y).sub_const 2).div_const 2).pow J).const_mul η
  have hbase : (Y 0 - 2) / 2 = α := by dsimp only [Y, r]; simp only [Matrix.cons_val_zero]; ring
  have haY : a Y = h := by dsimp only [a]; rw [hbase]
  have Hnear := (Hfreeze a ha haY).1
  have Hphase : terminalNaturalPhase η J =ᶠ[𝓝 Y] terminalConnectionPhase h := by
    filter_upwards [Hnear] with Z hZ
    change coreRadius (terminalConnectionState (a Z) Z 0) (terminalConnectionState (a Z) Z 2) =
      coreRadius (terminalConnectionState h Z 0) (terminalConnectionState h Z 2)
    rw [hZ.2]
  have Hnatural : ContDiffAt ℝ 2 (terminalNaturalPhase η J) Y := Hf.congr_of_eventuallyEq Hphase
  have Hder : fderiv ℝ (terminalNaturalPhase η J) Y = fderiv ℝ (terminalConnectionPhase h) Y := Hphase.fderiv_eq
  let d : ExitTailState := ![1, deriv U r, deriv W r]
  have Hdir := (Hcone d rfl hUd hWd).1
  change |α ^ 2 * fderiv ℝ (terminalConnectionPhase h) Y d + 1| ≤ A * Real.sqrt b at Hdir
  rw [← Hder] at Hdir
  obtain ⟨Hφ, Hneg, g, Hg, Hlog⟩ := exists_graph_phase_inverse Hnatural hU hW hα.1 Hsmall Hdir
  refine ⟨HV, Hφ, Hneg, g, Hg, ?_⟩
  simpa only [mul_assoc] using Hlog

end BianchiIX
