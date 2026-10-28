import BianchiIX.Analysis.ReciprocalDifference
import BianchiIX.Dynamics.TerminalConnectionDifferential

noncomputable section

namespace BianchiIX

def terminalReciprocalError (h : ℝ) (Y : ExitTailState) : ℝ :=
  2 / terminalConnectionPhase h Y - 2 / terminalEntranceInput h Y 0

theorem terminalReciprocalError_differential {h : ℝ} {Y : ExitTailState}
    (hΘ : ContDiffAt ℝ 2 (terminalConnectionError h) Y)
    (hr : ContDiffAt ℝ 2 (terminalEntranceInput h) Y)
    (hF0 : terminalConnectionPhase h Y ≠ 0) (hr0 : terminalEntranceInput h Y 0 ≠ 0) :
    ContDiffAt ℝ 2 (terminalReciprocalError h) Y ∧
      terminalReciprocalError h Y = -2 * terminalConnectionError h Y /
        (terminalEntranceInput h Y 0 * terminalConnectionPhase h Y) ∧
      ∀ d : ExitTailState, fderiv ℝ (terminalReciprocalError h) Y d =
        -2 * fderiv ℝ (terminalConnectionError h) Y d / (terminalConnectionPhase h Y) ^ 2 +
          2 * terminalConnectionError h Y * (terminalConnectionPhase h Y + terminalEntranceInput h Y 0) *
            fderiv ℝ (fun Z => terminalEntranceInput h Z 0) Y d /
              ((terminalEntranceInput h Y 0) ^ 2 * (terminalConnectionPhase h Y) ^ 2) := by
  have HR := contDiffAt_pi.mp hr 0
  have Heq : terminalConnectionPhase h = fun Z => terminalConnectionError h Z + terminalEntranceInput h Z 0 := by
    funext Z
    simp only [terminalConnectionError, sub_add_cancel]
  have HF : ContDiffAt ℝ 2 (terminalConnectionPhase h) Y := by
    rw [Heq]
    exact hΘ.add HR
  exact reciprocal_difference_differential HF HR hF0 hr0

end BianchiIX
