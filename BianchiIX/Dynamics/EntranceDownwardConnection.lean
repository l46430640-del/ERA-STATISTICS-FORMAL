import BianchiIX.Dynamics.EntranceDownwardReturn
import BianchiIX.Dynamics.PartialCoreDownwardConnection

noncomputable section

namespace BianchiIX

open Set

/-- A preceding upward entrance leads to a finite long connection on the same exact orbit. -/
theorem entrancePartialCore_connection_domain {y : ProjectiveState} {η : ℝ}
    (hk : 8 ≤ coreRadius (y 0) (y 2)) (hm : 1 ≤ y 0)
    (hu : 0 < y 1 ∧ y 1 ≤ 1 / 10000) (hv : 0 < y 2 ∧ y 2 < 1)
    (hw : 0 < y 3 ∧ y 3 ≤ 1 / 10000) (hη : 0 < η ∧ η ≤ 1 / 10000)
    (hsmall : y 1 + y 2 * y 3 ≤ η / (2 * coreRadius (y 0) (y 2))) :
    let z := entranceReturnState y
    let κ := coreRadius (z 0) (z 2)
    let T := partialCoreDownwardReturnTime y
    let out := projectiveOriginalFlow y 0 T
    let p := coreExitConnectionParameters (partialCoreDownwardReturnState y)
    0 < T ∧ out = connectionEntry (p 0) (p 1) (p 2) ∧
      (4 ≤ p 0 ∧ κ / 2 ≤ p 0 ∧ p 0 < κ) ∧
      (0 < p 1 ∧ p 1 ≤ η / p 0) ∧ (0 < p 2 ∧ p 2 ≤ η) ∧
      p 1 ≤ z 1 * Real.exp (-κ / 12) ∧ p 2 ≤ z 3 ∧
      phaseNorm (p 0 + 1) 1 = partialCoreDownwardReturnState y 0 ∧
      1 < partialCoreDownwardReturnState y 0 ∧
      connectionReturnValid p ∧ ContDiffAt ℝ 2 connectionReturnTime p ∧
      ContDiffAt ℝ 2 connectionReturnState p ∧
      connectionReturnState p = projectiveOriginalFlow y 0 (T + connectionReturnTime p) ∧
      let Q := fun w => coreExitConnectionParameters (partialCoreDownwardReturnState w)
      ContDiffAt ℝ 2 Q y ∧
        ContDiffAt ℝ 2 (fun w => partialCoreDownwardReturnTime w + connectionReturnTime (Q w)) y ∧
        ContDiffAt ℝ 2 (fun w => connectionReturnState (Q w)) y := by
  intro z κ T out p
  have hk' : 7 / 4 ≤ coreRadius (y 0) (y 2) := by linarith only [hk]
  have HE := entranceReturn_regular hk' hm ⟨hu.1.le, hu.2⟩ hv ⟨hw.1.le, hw.2⟩
  have hS := HE.1.1.1.1
  obtain ⟨hκ, _, hhit, hmz, hregion, _, _, hsum, hangle⟩ :=
    entranceReturn_partialCore_entry hk hm ⟨hu.1.le, hu.2⟩ hv ⟨hw.1.le, hw.2⟩ hη hsmall
  have Hpos := entranceReturn_walls_pos hk' hm hu hv hw _ ⟨hS.le, le_rfl⟩
  change 0 < z 1 ∧ 0 < z 2 ∧ 0 < z 3 at Hpos
  have hprod : 0 < z 2 * z 3 := mul_pos Hpos.2.1 Hpos.2.2
  have hUη : z 1 ≤ η / κ := (le_add_of_nonneg_right hprod.le).trans hsum
  have hPη : z 2 * z 3 ≤ η / κ := (le_add_of_nonneg_left Hpos.1.le).trans hsum
  have hκZ : 2 * Real.cosh 0 ≤ κ := by
    rw [Real.cosh_zero]
    change 6 ≤ κ at hκ
    linarith only [hκ]
  have hz : projectiveCoreAngle z ≤ 0 := by
    rw [hangle]
    exact neg_nonpos.mpr (Real.arcosh_nonneg (by linarith only [hκ]))
  obtain ⟨hdown, htime, hstate, hct, hcs, _⟩ := entrancePartialCore_downward_regular
    hk hm ⟨hu.1.le, hu.2⟩ hv ⟨hw.1.le, hw.2⟩ hη hsmall
  have hp : p = coreExitConnectionParameters (partialCoreDownwardReturnState z) :=
    congrArg coreExitConnectionParameters hstate
  obtain ⟨hentry, hμ, hU, hW, hdecU, hdecW, hphase, _, hvalid, hcT, hcP, horbit⟩ :=
    partialCoreDownwardReturn_connection_domain hκ hregion rfl (Or.inr ⟨hhit, hmz.le⟩)
      (le_refl (0 : ℝ)) hκZ hz hη ⟨Hpos.1, hUη⟩ ⟨hprod, hPη⟩
  rw [← hp] at hentry hμ hU hW hdecU hdecW hphase hvalid hcT hcP horbit
  have hD := entrance_initial_denom_pos hk' hm ⟨hu.1.le, hu.2⟩ hv ⟨hw.1.le, hw.2⟩
  have HA := (HE.1.2.1 _ ⟨hS.le, le_rfl⟩).2
  have Hrestart (t : ℝ) (ht : 0 ≤ t) :
      projectiveOriginalFlow z 0 t = projectiveOriginalFlow y 0 (entranceReturnTime y + t) := by
    change projectiveOriginalFlow (projectiveOriginalFlow y 0 (entranceReturnTime y)) 0 t = _
    simpa only [add_comm t (entranceReturnTime y)] using projectiveOriginalFlow_restart hD hS.le ht HA
  have hTz : 0 < partialCoreDownwardReturnTime z :=
    (partialCoreDownwardReturn_regular hκ hregion rfl (Or.inr ⟨hhit, hmz.le⟩)).1.1.1
  have hout : out = projectiveOriginalFlow z 0 (partialCoreDownwardReturnTime z) := by
    change projectiveOriginalFlow y 0 (partialCoreDownwardReturnTime y) = _
    rw [htime]
    exact (Hrestart _ hTz.le).symm
  have hphase' : phaseNorm (p 0 + 1) 1 = partialCoreDownwardReturnState y 0 := by
    change phaseNorm (p 0 + 1) 1 = coreRadius (out 0) (out 2)
    rw [hout]
    exact hphase
  have hK : 1 < partialCoreDownwardReturnState y 0 := by
    have H := phaseNorm_ge (b := 1) (show 0 ≤ p 0 + 1 by linarith only [hμ.1])
    rw [hphase'] at H
    linarith only [H, hμ.1]
  refine ⟨hdown.1.1, hout.trans hentry, hμ, hU, hW, hdecU, ?_, hphase', hK,
    hvalid, hcT, hcP, ?_, ?_⟩
  · simpa only [hhit, one_mul] using hdecW
  · have htc : 0 < connectionReturnTime p := hvalid.1.1.1
    calc
      _ = projectiveOriginalFlow z 0 (partialCoreDownwardReturnTime z + connectionReturnTime p) := horbit
      _ = projectiveOriginalFlow y 0
          (entranceReturnTime y + (partialCoreDownwardReturnTime z + connectionReturnTime p)) :=
        Hrestart _ (add_nonneg hTz.le htc.le)
      _ = _ := by change _ = projectiveOriginalFlow y 0 (partialCoreDownwardReturnTime y + _); rw [htime, add_assoc]
  · intro Q
    have hcQ : ContDiffAt ℝ 2 Q y := (contDiffAt_coreExitConnectionParameters 2 hK).comp y hcs
    exact ⟨hcQ, hct.add (ContDiffAt.comp (g := connectionReturnTime) y hcT hcQ),
      ContDiffAt.comp (g := connectionReturnState) y hcP hcQ⟩

end BianchiIX
