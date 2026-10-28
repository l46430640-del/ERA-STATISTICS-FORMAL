import BianchiIX.Dynamics.CoreTailMultipliers
import BianchiIX.Dynamics.TerminalEntranceDerivativeBounds

noncomputable section

namespace BianchiIX

open Filter
open scoped Topology

/-- Indices 0 and 1 transport the old U and W walls to the new w and v walls, respectively. -/
def terminalWallFactor (h : ℝ) (Y : ExitTailState) (i : Fin 2) : ℝ :=
  4 * coreTailMultiplier h Y i / projectiveCycleDenom (coreTailState h Y)

theorem terminalWallFactor_pos {h : ℝ} {Y : ExitTailState}
    (hH : 0 < projectiveCycleDenom (coreTailState h Y)) (i : Fin 2) :
    0 < terminalWallFactor h Y i :=
  div_pos (mul_pos (by norm_num) (coreTailMultiplier_pos h Y i)) hH

theorem terminalEntranceInput_wall_factors {h : ℝ} {Y : ExitTailState} (HV : coreTailValid h Y) :
    terminalEntranceInput h Y 1 = 4 * h / projectiveCycleDenom (coreTailState h Y) ∧
      terminalEntranceInput h Y 2 = Y 2 * terminalWallFactor h Y 1 ∧
      terminalEntranceInput h Y 3 = Y 1 * terminalWallFactor h Y 0 := by
  have H0 := coreTailMultiplier_formula HV 0
  have H1 := coreTailMultiplier_formula HV 1
  change coreTailState h Y 1 = Y 1 * coreTailMultiplier h Y 0 at H0
  change coreTailState h Y 3 = Y 2 * coreTailMultiplier h Y 1 at H1
  change (4 * coreTailState h Y 2 / _ = _) ∧ (4 * coreTailState h Y 3 / _ = _) ∧
    (4 * coreTailState h Y 1 / _ = _)
  rw [coreTailState_active HV, H0, H1]
  dsimp only [terminalWallFactor]
  constructor
  · rfl
  · constructor <;> ring

theorem contDiffAt_terminalWallFactor_two {h : ℝ} {Y : ExitTailState}
    (hR : 1 < Y 0) (HV : coreTailValid h Y)
    (hH : 0 < projectiveCycleDenom (coreTailState h Y)) (i : Fin 2) :
    ContDiffAt ℝ 2 (fun Z => terminalWallFactor h Z i) Y ∧
      ContDiffAt ℝ 2 (fun Z => Real.log (terminalWallFactor h Z i)) Y := by
  have HR := coreTail_regular_of_valid hR HV
  have HM := (contDiffAt_coreTailMultiplier_two hR HV HR.1 i).1
  have HD : ContDiffAt ℝ 2 (fun Z => projectiveCycleDenom (coreTailState h Z)) Y :=
    ContDiffAt.comp (g := projectiveCycleDenom) (f := coreTailState h) Y
    (contDiff_projectiveCycleDenom 2).contDiffAt HR.2.1
  have HB : ContDiffAt ℝ 2 (fun Z => terminalWallFactor h Z i) Y :=
    (contDiffAt_const.mul HM).div HD hH.ne'
  exact ⟨HB, HB.log (terminalWallFactor_pos hH i).ne'⟩

theorem terminalWallFactor_log_fderiv {h : ℝ} {Y : ExitTailState}
    (hR : 1 < Y 0) (HV : coreTailValid h Y)
    (hH : 0 < projectiveCycleDenom (coreTailState h Y)) (i : Fin 2) :
    fderiv ℝ (fun Z => Real.log (terminalWallFactor h Z i)) Y =
      fderiv ℝ (fun Z => Real.log (coreTailMultiplier h Z i)) Y -
        fderiv ℝ (fun Z => Real.log (projectiveCycleDenom (coreTailState h Z))) Y := by
  have HR := coreTail_regular_of_valid hR HV
  have HM := (contDiffAt_coreTailMultiplier_two hR HV HR.1 i).2.differentiableAt (by norm_num)
  have HD : ContDiffAt ℝ 2 (fun Z => projectiveCycleDenom (coreTailState h Z)) Y :=
    ContDiffAt.comp (g := projectiveCycleDenom) (f := coreTailState h) Y
    (contDiff_projectiveCycleDenom 2).contDiffAt HR.2.1
  have HL := (HD.log hH.ne').differentiableAt (by norm_num)
  have HE : (fun Z => Real.log (terminalWallFactor h Z i)) =ᶠ[𝓝 Y]
      (fun Z => Real.log 4 + Real.log (coreTailMultiplier h Z i) -
        Real.log (projectiveCycleDenom (coreTailState h Z))) := by
    filter_upwards [HD.continuousAt.eventually_ne hH.ne'] with Z hZ
    rw [terminalWallFactor, Real.log_div (mul_ne_zero (by norm_num) (coreTailMultiplier_pos h Z i).ne') hZ,
      Real.log_mul (by norm_num) (coreTailMultiplier_pos h Z i).ne']
  rw [HE.fderiv_eq, fderiv_fun_sub (HM.const_add (Real.log 4)) HL, fderiv_const_add]

/-- Fixed height makes the new active-wall logarithmic derivative exactly minus that of the cyclic denominator. -/
theorem terminalEntranceInput_active_log_fderiv {h : ℝ} {Y : ExitTailState}
    (hR : 1 < Y 0) (HV : coreTailValid h Y) (hh : 0 < h)
    (hH : 0 < projectiveCycleDenom (coreTailState h Y)) :
    fderiv ℝ (fun Z => Real.log (terminalEntranceInput h Z 1)) Y =
      -fderiv ℝ (fun Z => Real.log (projectiveCycleDenom (coreTailState h Z))) Y := by
  have HR := coreTail_regular_of_valid hR HV
  have HD : ContDiffAt ℝ 2 (fun Z => projectiveCycleDenom (coreTailState h Z)) Y :=
    ContDiffAt.comp (g := projectiveCycleDenom) (f := coreTailState h) Y
    (contDiff_projectiveCycleDenom 2).contDiffAt HR.2.1
  have HE : (fun Z => Real.log (terminalEntranceInput h Z 1)) =ᶠ[𝓝 Y]
      (fun Z => Real.log (4 * h) - Real.log (projectiveCycleDenom (coreTailState h Z))) := by
    filter_upwards [HR.2.2, HD.continuousAt.eventually_ne hH.ne'] with Z hZ hZD
    rw [(terminalEntranceInput_wall_factors hZ).1,
      Real.log_div (mul_ne_zero (by norm_num) hh.ne') hZD]
  rw [HE.fderiv_eq, fderiv_const_sub]

end BianchiIX
