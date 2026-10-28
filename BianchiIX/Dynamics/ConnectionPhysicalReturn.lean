import BianchiIX.Dynamics.ConnectionReturnPhaseBoundary
import BianchiIX.Analysis.ThreeCoordinateLinear

noncomputable section

namespace BianchiIX

def connectionReturnPhysicalState (p : ConnectionParameters) : ConnectionParameters :=
  ![phaseNorm (-connectionReturnState p 0 - 1) 1, connectionReturnState p 1, connectionReturnState p 2]

theorem hasFDerivAt_connectionEntrancePhase (p : ConnectionParameters) :
    HasFDerivAt (fun q : ConnectionParameters => phaseNorm (q 0 + 1) 1)
      (((p 0 + 1) / phaseNorm (p 0 + 1) 1) •
        (ContinuousLinearMap.proj (0 : Fin 3) : ConnectionParameters →L[ℝ] ℝ)) p := by
  have ha := (hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 3) p).add_const 1
  have H := ((ha.pow 2).add_const 1).sqrt (by positivity : (p 0 + 1) ^ 2 + 1 ≠ 0)
  convert! H using 1
  · ext q
    simp [phaseNorm]
  · ext v
    simp only [smul_apply, smul_eq_mul, ContinuousLinearMap.proj_apply]
    simp only [phaseNorm, one_pow]
    ring

theorem contDiffAt_connectionReturnPhysicalState {p : ConnectionParameters} (hμ : 4 ≤ p 0)
    (hu : 0 ≤ p 1 ∧ p 1 ≤ (1 / 10000) / p 0) (hw : 0 < p 2 ∧ p 2 ≤ 1 / 10000) :
    ContDiffAt ℝ 2 connectionReturnPhysicalState p := by
  have hstate := (connectionReturn_regular hμ hu hw).2.2.1
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i
  · have hm := contDiffAt_pi.mp hstate 0
    exact ((((hm.neg.sub contDiffAt_const).pow 2).add contDiffAt_const).sqrt (by positivity))
  · exact contDiffAt_pi.mp hstate 1
  · exact contDiffAt_pi.mp hstate 2

/-- Physical output differentials use the entrance phase and the ordinary phase error. -/
theorem connectionReturnPhysicalState_differential {p : ConnectionParameters} (hμ : 4 ≤ p 0)
    (hu : 0 < p 1 ∧ p 1 ≤ (1 / 10000) / p 0) (hw : 0 < p 2 ∧ p 2 ≤ 1 / 10000)
    (v : ConnectionParameters) :
    let d := fderiv ℝ connectionReturnPhysicalState p v
    let J := fderiv ℝ (connectionLogCoordinates ∘ connectionReturnState) p v
    d 0 = ((p 0 + 1) / phaseNorm (p 0 + 1) 1) * v 0 + fderiv ℝ connectionReturnPhaseError p v ∧
      d 1 = connectionReturnState p 1 * J 1 ∧ d 2 = connectionReturnState p 2 * J 2 := by
  intro d J
  have hu' : 0 ≤ p 1 ∧ p 1 ≤ (1 / 10000) / p 0 := ⟨hu.1.le, hu.2⟩
  have hphys := (contDiffAt_connectionReturnPhysicalState hμ hu' hw).differentiableAt (by norm_num)
  have hstate := (connectionReturn_regular hμ hu' hw).2.2.1.differentiableAt (by norm_num)
  have herror := (contDiffAt_connectionReturnPhaseError hμ hu' hw).differentiableAt (by norm_num)
  have hphase : (fun q => connectionReturnPhysicalState q 0) =
      (fun q => phaseNorm (q 0 + 1) 1 - 2 + connectionReturnPhaseError q) := by
    ext q
    dsimp [connectionReturnPhysicalState, connectionReturnPhaseError]
    ring
  have hraw : d 0 = ((p 0 + 1) / phaseNorm (p 0 + 1) 1) * v 0 + fderiv ℝ connectionReturnPhaseError p v := by
    have Hd := congrArg (fun A : ConnectionParameters →L[ℝ] ℝ => A v)
      (((hasFDerivAt_connectionEntrancePhase p).sub_const 2).add herror.hasFDerivAt).fderiv
    change fderiv ℝ (fun q => phaseNorm (q 0 + 1) 1 - 2 + connectionReturnPhaseError q) p v = _ at Hd
    rw [← hphase, fderiv_apply hphys 0] at Hd
    exact Hd
  have hc := connectionReturn_control hμ hu' hw
  have hr := (hc.2 (connectionReturnTime p) ⟨hc.1.le, le_rfl⟩).2
  change connectionRegion (p 0) (connectionReturnState p) at hr
  have hm : 1 < -connectionReturnState p 0 := by linarith only [hμ, (abs_le.mp hr.1).1]
  have hpos := connectionReturn_wall_pos hμ hu' hw
  have hU := ne_of_gt (hpos.2 hu.1)
  have hV := ne_of_gt hpos.1
  have hW : connectionReturnState p 3 ≠ 0 := by
    rw [(connectionReturn_growing_component hμ hu' hw).1]
    norm_num
  have hJ : J = connectionLogTangent (connectionReturnState p) (fderiv ℝ connectionReturnState p v) := by
    dsimp [J]
    rw [fderiv_comp p ((contDiffAt_connectionLogCoordinates 1 hm hU hV hW).differentiableAt (by norm_num)) hstate,
      ContinuousLinearMap.comp_apply, connectionLogCoordinates_fderiv hm hU hV hW]
  have hcomponent (i : Fin 2) : d i.succ = fderiv ℝ connectionReturnState p v i.succ.castSucc := by
    have heq : (fun q => connectionReturnPhysicalState q i.succ) = (fun q => connectionReturnState q i.succ.castSucc) := by
      ext q
      fin_cases i <;> rfl
    have HH := congrArg (fun f : ConnectionParameters → ℝ => fderiv ℝ f p) heq
    rw [fderiv_apply hphys i.succ, fderiv_apply hstate i.succ.castSucc] at HH
    exact congrArg (fun A : ConnectionParameters →L[ℝ] ℝ => A v)
      HH
  refine ⟨hraw, ?_, ?_⟩
  · have Hc : d 1 = fderiv ℝ connectionReturnState p v 1 := hcomponent 0
    rw [Hc, hJ]
    change _ = connectionReturnState p 1 * (_ / connectionReturnState p 1)
    field_simp
  · have Hc : d 2 = fderiv ℝ connectionReturnState p v 2 := hcomponent 1
    rw [Hc, hJ]
    change _ = connectionReturnState p 2 * (_ / connectionReturnState p 2)
    field_simp

end BianchiIX
