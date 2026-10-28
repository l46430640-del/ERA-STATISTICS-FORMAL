import BianchiIX.Dynamics.TerminalConnection
import BianchiIX.Dynamics.TerminalWallFactors
import BianchiIX.Dynamics.EntranceRadialInverse

noncomputable section

namespace BianchiIX

open Filter
open scoped Topology

def terminalConnectionPhase (h : ℝ) (Y : ExitTailState) : ℝ :=
  coreRadius (terminalConnectionState h Y 0) (terminalConnectionState h Y 2)

def terminalConnectionError (h : ℝ) (Y : ExitTailState) : ℝ :=
  terminalConnectionPhase h Y - terminalEntranceInput h Y 0

theorem terminalEntranceInput_fderiv {h : ℝ} {Y : ExitTailState}
    (hR : 1 < Y 0) (HV : coreTailValid h Y) (hh : 0 < h)
    (hH : 0 < projectiveCycleDenom (coreTailState h Y))
    (hc : ContDiffAt ℝ 2 (terminalEntranceInput h) Y) (v : ExitTailState) :
    fderiv ℝ (terminalEntranceInput h) Y v =
      ![fderiv ℝ (fun Z => terminalEntranceInput h Z 0) Y v,
        terminalEntranceInput h Y 1 * fderiv ℝ (fun Z => Real.log (terminalEntranceInput h Z 1)) Y v,
        v 2 * terminalWallFactor h Y 1 + terminalEntranceInput h Y 2 *
          fderiv ℝ (fun Z => Real.log (terminalWallFactor h Z 1)) Y v,
        v 1 * terminalWallFactor h Y 0 + terminalEntranceInput h Y 3 *
          fderiv ℝ (fun Z => Real.log (terminalWallFactor h Z 0)) Y v] := by
  have hd := hc.differentiableAt (by norm_num)
  have Hnear := (coreTail_regular_of_valid hR HV).2.2
  have Hwall (i : Fin 2) :
      fderiv ℝ (terminalEntranceInput h) Y v (if i = 0 then 3 else 2) =
        v i.succ * terminalWallFactor h Y i +
        terminalEntranceInput h Y (if i = 0 then 3 else 2) *
          fderiv ℝ (fun Z => Real.log (terminalWallFactor h Z i)) Y v := by
    have hm := (contDiffAt_terminalWallFactor_two hR HV hH i).1.differentiableAt (by norm_num)
    have HE : (fun Z => terminalEntranceInput h Z (if i = 0 then 3 else 2)) =ᶠ[𝓝 Y]
        (fun Z => Z i.succ * terminalWallFactor h Z i) := by
      filter_upwards [Hnear] with Z hZ
      fin_cases i
      · exact (terminalEntranceInput_wall_factors hZ).2.2
      · exact (terminalEntranceInput_wall_factors hZ).2.1
    have HD := (hasFDerivAt_apply (𝕜 := ℝ) i.succ Y).mul hm.hasFDerivAt
    have H := congrArg (fun L : ExitTailState →L[ℝ] ℝ => L v) (HE.fderiv_eq.trans HD.fderiv)
    rw [fderiv_apply hd] at H
    have HM : fderiv ℝ (fun Z => terminalWallFactor h Z i) Y v = terminalWallFactor h Y i *
        fderiv ℝ (fun Z => Real.log (terminalWallFactor h Z i)) Y v := by
      rw [(hm.hasFDerivAt.log (terminalWallFactor_pos hH i).ne').fderiv]
      simp only [smul_apply, smul_eq_mul]
      field_simp [(terminalWallFactor_pos hH i).ne']
    have HEY : terminalEntranceInput h Y (if i = 0 then 3 else 2) = Y i.succ * terminalWallFactor h Y i := HE.self_of_nhds
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
      add_apply, smul_apply, smul_eq_mul] at H
    rw [H, HM, HEY]
    ring
  ext i
  fin_cases i
  · exact (congrArg (fun L : ExitTailState →L[ℝ] ℝ => L v) (fderiv_apply hd 0)).symm
  · have hf := (hasFDerivAt_pi'.mp hd.hasFDerivAt 1)
    change fderiv ℝ (terminalEntranceInput h) Y v 1 = terminalEntranceInput h Y 1 *
      fderiv ℝ (fun Z => Real.log (terminalEntranceInput h Z 1)) Y v
    have hp : 0 < terminalEntranceInput h Y 1 := by
      rw [(terminalEntranceInput_wall_factors HV).1]
      exact div_pos (mul_pos (by norm_num) hh) hH
    rw [(hf.log hp.ne').fderiv]
    simp only [smul_apply, smul_eq_mul, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]
    field_simp [hp.ne']
  · exact Hwall 1
  · exact Hwall 0

theorem terminalConnectionError_chart_germ {h : ℝ} {Y : ExitTailState}
    {Ψ : ProjectiveState → ProjectiveState} (HΨ : EntranceRadialInverseAt (terminalCyclicInput h Y) Ψ)
    (hc : ContinuousAt (terminalCyclicInput h) Y) :
    terminalConnectionError h =ᶠ[𝓝 Y] (fun Z =>
      coreRadius (entranceReturnState (Ψ (terminalEntranceInput h Z)) 0)
        (entranceReturnState (Ψ (terminalEntranceInput h Z)) 2) - terminalEntranceInput h Z 0) := by
  filter_upwards [hc.tendsto.eventually HΨ.left_inverse] with Z hZ
  change terminalConnectionPhase h Z - terminalEntranceInput h Z 0 = _
  change Ψ (terminalEntranceInput h Z) = terminalCyclicInput h Z at hZ
  rw [hZ]
  rfl

/-- The four entrance columns compose to the actual terminal phase error at fixed auxiliary height. -/
theorem terminalConnectionError_differential {h : ℝ} {Y : ExitTailState}
    (hR : 1 < Y 0) (HV : coreTailValid h Y) (hh : 0 < h)
    (hH : 0 < projectiveCycleDenom (coreTailState h Y))
    (hc : ContDiffAt ℝ 2 (terminalEntranceInput h) Y)
    {Ψ : ProjectiveState → ProjectiveState} (HΨ : EntranceRadialInverseAt (terminalCyclicInput h Y) Ψ)
    (hF : ContDiffAt ℝ 2 (fun z => coreRadius (entranceReturnState (Ψ z) 0)
      (entranceReturnState (Ψ z) 2)) (terminalEntranceInput h Y)) :
    ContDiffAt ℝ 2 (terminalConnectionError h) Y ∧ ∀ v : ExitTailState,
      let z := terminalEntranceInput h Y
      let F := fun z => coreRadius (entranceReturnState (Ψ z) 0) (entranceReturnState (Ψ z) 2)
      fderiv ℝ (terminalConnectionError h) Y v =
        (fderiv ℝ F z (Pi.single 0 1) - 1) * fderiv ℝ (fun Z => terminalEntranceInput h Z 0) Y v +
        fderiv ℝ F z (Pi.single 1 1) * (z 1 * fderiv ℝ (fun Z => Real.log (terminalEntranceInput h Z 1)) Y v) +
        fderiv ℝ F z (Pi.single 2 1) * (v 2 * terminalWallFactor h Y 1 + z 2 *
          fderiv ℝ (fun Z => Real.log (terminalWallFactor h Z 1)) Y v) +
        fderiv ℝ F z (Pi.single 3 1) * (v 1 * terminalWallFactor h Y 0 + z 3 *
          fderiv ℝ (fun Z => Real.log (terminalWallFactor h Z 0)) Y v) := by
  let F := fun z => coreRadius (entranceReturnState (Ψ z) 0) (entranceReturnState (Ψ z) 2)
  have Htail := (coreTail_regular_of_valid hR HV).2.1
  have Hcyc : ContDiffAt ℝ 2 (terminalCyclicInput h) Y :=
    ContDiffAt.comp (g := projectiveCycle) (f := coreTailState h) Y
      (contDiffAt_projectiveCycle 2 hH.ne') Htail
  have HE := terminalConnectionError_chart_germ HΨ Hcyc.continuousAt
  have Hr : ContDiffAt ℝ 2 (fun Z => terminalEntranceInput h Z 0) Y := (contDiffAt_pi.mp hc) 0
  have Hreg := (ContDiffAt.comp (g := F) (f := terminalEntranceInput h) Y hF hc).sub Hr
  refine ⟨Hreg.congr_of_eventuallyEq HE, ?_⟩
  intro v z F
  have HD := ((hF.differentiableAt (by norm_num)).hasFDerivAt.comp Y
    (hc.differentiableAt (by norm_num)).hasFDerivAt).sub (Hr.differentiableAt (by norm_num)).hasFDerivAt
  change HasFDerivAt (fun Z => coreRadius (entranceReturnState (Ψ (terminalEntranceInput h Z)) 0)
    (entranceReturnState (Ψ (terminalEntranceInput h Z)) 2) - terminalEntranceInput h Z 0) _ Y at HD
  rw [HE.fderiv_eq, HD.fderiv]
  simp only [sub_apply, ContinuousLinearMap.comp_apply]
  rw [terminalEntranceInput_fderiv hR HV hh hH hc v]
  have Hlin (a b c d : ℝ) : fderiv ℝ F z ![a, b, c, d] =
      a * fderiv ℝ F z (Pi.single 0 1) + b * fderiv ℝ F z (Pi.single 1 1) +
      c * fderiv ℝ F z (Pi.single 2 1) + d * fderiv ℝ F z (Pi.single 3 1) := by
    have H : (![a, b, c, d] : ProjectiveState) =
        a • Pi.single 0 1 + b • Pi.single 1 1 + c • Pi.single 2 1 + d • Pi.single 3 1 := by
      ext i
      fin_cases i <;> simp
    rw [H, map_add, map_add, map_add, map_smul, map_smul, map_smul, map_smul]
    rfl
  rw [Hlin]
  ring

end BianchiIX
