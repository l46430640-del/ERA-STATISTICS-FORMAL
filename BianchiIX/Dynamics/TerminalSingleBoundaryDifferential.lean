import BianchiIX.Dynamics.ExitSingleBoundaryDifferential
import BianchiIX.Dynamics.TerminalSinglePhaseGerm
import BianchiIX.Dynamics.CoreTailReferenceDifferential

noncomputable section

namespace BianchiIX

open Filter
open scoped Topology

/-- Compose the single-wall phase with the actual finite tail before taking any late-height limit. -/
theorem terminalSinglePhase_boundary_differential {R h : ℝ} (hR : 2 < R) (hh : 0 < h ∧ h < 1) :
    terminalSinglePhase h ![R, 0, 0] = (R - 2) / 2 ∧
      ContDiffAt ℝ 2 (terminalSinglePhase h) ![R, 0, 0] ∧ ∀ d : ExitTailState,
      fderiv ℝ (terminalSinglePhase h) ![R, 0, 0] d = d 0 / 2 +
        (-1 / R + (1 / R + exitSingleBoundarySlope R h) *
          Real.exp (-(R ^ 2 / 2) * referenceTailDuration R h)) * d 1 +
        (exitSingleBoundarySlope R h * Real.exp (-2 * referenceTailDuration R h)) * d 2 := by
  have hR1 : 1 < R := by linarith only [hR]
  have hR0 : 0 < R := by linarith only [hR]
  have hv : h ^ 2 < R ^ 2 := by nlinarith only [hR, hh.1, hh.2]
  have hH : 0 < exitSingleBase R h :=
    (sq_pos_of_pos (sub_pos.mpr hR)).trans_le (exitSingleBase_boundary_lower hR hv.le)
  let Y : ExitTailState := ![R, 0, 0]
  let F := fun Z => toExitTailState (coreTailState h Z)
  let f := fun Z : ExitTailState => exitSinglePhase (Z 0) (Z 1) h (Z 2)
  have HR := coreTail_reference_regular hR1 hh
  have HV := HR.2.2.2.2.self_of_nhds
  have Hcoord : F Y = Y := coreTail_reference_coordinates hR1 hh
  have hm : coreTailState h Y 0 < 1 := by
    rw [HR.2.1]
    change 1 - Real.sqrt (R ^ 2 - h ^ 2) < 1
    linarith only [Real.sqrt_pos.mpr (sub_pos.mpr hv)]
  have hV : 0 < coreTailState h Y 2 := by rw [HR.2.1]; exact hh.1
  have HF : ContDiffAt ℝ 2 F Y := (contDiffAt_toExitTailState 2 hV).comp Y HR.2.2.2.1
  have Hf := exitSinglePhase_boundary_differential hR hv
  change ContDiffAt ℝ 2 f Y ∧ _ at Hf
  have HE := terminalSinglePhase_eventuallyEq_radical hR1 HV hm HF.continuousAt
    (by change h ^ 2 < (F Y 0) ^ 2; rw [Hcoord]; exact hv)
    (by change 0 < exitSingleBase (F Y 0) h; rw [Hcoord]; exact hH)
    (by change 0 < exitSingleBase (F Y 0) h + exitSingleDefect (F Y 1) h (F Y 2)
        rw [Hcoord]; simpa [Y, exitSingleDefect] using hH)
    (by change 0 < (F Y 0) ^ 2 - 4 + exitSingleDefect (F Y 1) h (F Y 2)
        rw [Hcoord]
        simpa [Y, exitSingleDefect] using (show 0 < R ^ 2 - 4 by nlinarith only [hR]))
  change terminalSinglePhase h =ᶠ[𝓝 Y] f ∘ F at HE
  have HfF : ContDiffAt ℝ 2 f (F Y) := Hcoord.symm ▸ Hf.1
  have Hreg := (HfF.comp Y HF).congr_of_eventuallyEq HE
  have Hder : fderiv ℝ (terminalSinglePhase h) Y = (fderiv ℝ f (F Y)).comp (fderiv ℝ F Y) :=
    HE.fderiv_eq.trans (fderiv_comp Y (HfF.differentiableAt (by norm_num)) (HF.differentiableAt (by norm_num)))
  refine ⟨?_, Hreg, ?_⟩
  · rw [HE.self_of_nhds]
    change f (F Y) = _
    rw [Hcoord]
    exact exitSinglePhase_zero hR0.le h
  · intro d
    change fderiv ℝ (terminalSinglePhase h) Y d = _
    rw [Hder, ContinuousLinearMap.comp_apply, Hcoord, Hf.2]
    have HD : fderiv ℝ F Y d = _ := coreTail_reference_differential hR1 hh d
    rw [HD]
    dsimp
    field_simp [hh.1.ne']
    ring

end BianchiIX
