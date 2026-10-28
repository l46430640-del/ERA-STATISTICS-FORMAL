import BianchiIX.Dynamics.TerminalSinglePhaseBounds
import BianchiIX.Dynamics.TerminalCyclicDerivativeBounds

noncomputable section

namespace BianchiIX

open Filter
open scoped Topology

def terminalSinglePhase (h : ℝ) (Y : ExitTailState) : ℝ :=
  singleStrongPhase (terminalCyclicInput h Y 0) (terminalCyclicInput h Y 1)

theorem exitSinglePhase_value_bound {α b R u v w : ℝ} (hα : 0 < α ∧ α ≤ 1)
    (hb : b ≤ α / 10000) (hR : |R - (2 + 2 * α)| ≤ α / 10000)
    (hw : |u| + |w| ≤ b) (hv : 0 ≤ v ∧ v ≤ α / 100) :
    |exitSinglePhase R u v w - (R - 2) / 2| ≤ 23 * b * (v + b) / α := by
  have HR := (exitSingle_terminal_geometry hα hb hR hw hv).1
  obtain ⟨HX, HE, _, _⟩ := exitSingle_terminal_error_bounds hα hb hR hw hv
  let X := Real.sqrt (R ^ 2 + exitSingleError R u v w)
  change 2 < X at HX
  have HS : X ^ 2 = R ^ 2 + exitSingleError R u v w :=
    Real.sq_sqrt (Real.sqrt_pos.mp (by linarith only [HX] : 0 < X)).le
  have HD : |X - R| ≤ |exitSingleError R u v w| := by
    have H := congrArg abs (show (X - R) * (X + R) = exitSingleError R u v w by nlinarith only [HS])
    rw [abs_mul, abs_of_pos (by linarith only [HR, HX] : 0 < X + R)] at H
    nlinarith only [H, HR, HX, abs_nonneg (X - R)]
  have Hid : exitSinglePhase R u v w - (R - 2) / 2 = (X - R) / 2 := by
    dsimp only [exitSinglePhase, X]; ring
  rw [Hid, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact (div_le_div_of_nonneg_right (HD.trans HE) (by norm_num)).trans_eq (by ring)

/-- The cyclic single-wall phase and its fixed-height radical agree on a full entrance neighborhood. -/
theorem terminalSinglePhase_eventuallyEq_radical {h : ℝ} {Y : ExitTailState}
    (hR : 1 < Y 0) (HV : coreTailValid h Y) (hm : coreTailState h Y 0 < 1)
    (hF : ContinuousAt (fun Z => toExitTailState (coreTailState h Z)) Y)
    (hsq : h ^ 2 < (toExitTailState (coreTailState h Y) 0) ^ 2)
    (hB : 0 < exitSingleBase (toExitTailState (coreTailState h Y) 0) h)
    (hD : 0 < exitSingleBase (toExitTailState (coreTailState h Y) 0) h +
      exitSingleDefect (toExitTailState (coreTailState h Y) 1) h (toExitTailState (coreTailState h Y) 2))
    (hN : 0 < (toExitTailState (coreTailState h Y) 0) ^ 2 - 4 +
      exitSingleDefect (toExitTailState (coreTailState h Y) 1) h (toExitTailState (coreTailState h Y) 2)) :
    terminalSinglePhase h =ᶠ[𝓝 Y] (fun Z =>
      exitSinglePhase (toExitTailState (coreTailState h Z) 0) (coreTailState h Z 1) h (coreTailState h Z 3)) := by
  let F := fun Z => toExitTailState (coreTailState h Z)
  have Hcore := coreTail_regular_of_valid hR HV
  have Hm : ∀ᶠ Z in 𝓝 Y, coreTailState h Z 0 < 1 :=
    ((continuous_apply 0).continuousAt.comp Hcore.2.1.continuousAt).eventually (isOpen_Iio.mem_nhds hm)
  have HA : Continuous (fun Q : ExitTailState => (Q 0) ^ 2 - h ^ 2) := by fun_prop
  have HB : Continuous (fun Q : ExitTailState => exitSingleBase (Q 0) h) := by
    unfold exitSingleBase exitTailGap; fun_prop
  have HT : Continuous (fun Q : ExitTailState => exitSingleDefect (Q 1) h (Q 2)) := by
    unfold exitSingleDefect; fun_prop
  have HD : Continuous (fun Q : ExitTailState => exitSingleBase (Q 0) h + exitSingleDefect (Q 1) h (Q 2)) := HB.add HT
  have HN : Continuous (fun Q : ExitTailState => (Q 0) ^ 2 - 4 + exitSingleDefect (Q 1) h (Q 2)) := by fun_prop
  have Ha := (HA.continuousAt.comp hF).eventually (isOpen_Ioi.mem_nhds (sub_pos.mpr hsq))
  have Hb := (HB.continuousAt.comp hF).eventually (isOpen_Ioi.mem_nhds hB)
  have Hd := (HD.continuousAt.comp hF).eventually (isOpen_Ioi.mem_nhds hD)
  have Hn := (HN.continuousAt.comp hF).eventually (isOpen_Ioi.mem_nhds hN)
  filter_upwards [Hcore.2.2, Hm, Ha, Hb, Hd, Hn] with Z hv hmZ ha hb hd hn
  let Q := F Z
  have Hactive := coreTailState_active hv
  have Hrec : fromExitTailState h Q = coreTailState h Z := by
    conv_lhs => rw [← Hactive]
    exact fromExitTailState_toExitTailState hmZ
  have HE := exitSinglePhase_eq_singleStrongPhase (sub_pos.mp ha).le hb hd hn
  change exitSinglePhase (Q 0) (Q 1) h (Q 2) = _ at HE
  change singleStrongPhase (projectiveCycle (coreTailState h Z) 0)
    (projectiveCycle (coreTailState h Z) 1) = exitSinglePhase (Q 0) (Q 1) h (Q 2)
  rw [← Hrec]
  convert HE.symm using 1
  dsimp [projectiveCycle, projectiveCycleDenom, fromExitTailState]
  congr 2; ring

end BianchiIX
