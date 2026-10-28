import BianchiIX.Dynamics.CoreTailBoundary
import BianchiIX.Dynamics.ProjectiveWallMultipliers

noncomputable section

namespace BianchiIX

open Set

def coreTailMultiplier (η : ℝ) (Y : CoreAngleState) (i : Fin 2) : ℝ :=
  normalizedProjectiveWallMultiplier (fromProjectiveState (coreTailEntry Y))
    (coreTailTime η Y) (if i = 0 then 0 else 2)

theorem coreTailMultiplier_pos (η : ℝ) (Y : CoreAngleState) (i : Fin 2) :
    0 < coreTailMultiplier η Y i := normalizedProjectiveWallMultiplier_pos _ _ _

theorem coreTailValid_denom_pos {η : ℝ} {Y : CoreAngleState} (hvalid : coreTailValid η Y) :
    0 < projectiveStateDenom (coreTailEntry Y) := by
  have hzero := (hvalid.2.1 0 ⟨le_rfl, hvalid.1.1.1.le⟩).2
  rw [normalizedMaxCurve_initial] at hzero
  change 0 < 1 + (6 / projectiveStateDenom (coreTailEntry Y) - 1) at hzero
  by_contra! hn
  have H := div_nonpos_of_nonneg_of_nonpos (by norm_num : (0 : ℝ) ≤ 6) hn
  linarith only [hzero, H]

theorem coreTailMultiplier_formula {η : ℝ} {Y : CoreAngleState} (hvalid : coreTailValid η Y)
    (i : Fin 2) : coreTailState η Y (if i = 0 then 1 else 3) = Y i.succ * coreTailMultiplier η Y i := by
  have hD := coreTailValid_denom_pos hvalid
  have hA0 := fromProjectiveState_clock_pos hD
  have hAT := (hvalid.2.1 (coreTailTime η Y) ⟨hvalid.1.1.1.le, le_rfl⟩).2
  have H := normalizedProjectiveWallMultiplier_formula hvalid.1.1.2.1 hA0 hAT
    (if i = 0 then 0 else 2)
  rw [toProjectiveState_fromProjectiveState hD.ne'] at H
  fin_cases i <;> exact H

theorem contDiffAt_coreTailMultiplier_two {η : ℝ} {Y : CoreAngleState}
    (hk : 1 < Y 0) (hvalid : coreTailValid η Y) (hτ : ContDiffAt ℝ 2 (coreTailTime η) Y)
    (i : Fin 2) :
    ContDiffAt ℝ 2 (fun Z => coreTailMultiplier η Z i) Y ∧
      ContDiffAt ℝ 2 (fun Z => Real.log (coreTailMultiplier η Z i)) Y := by
  have hD := coreTailValid_denom_pos hvalid
  have hc : ContDiffAt ℝ 2 (fun Z => fromProjectiveState (coreTailEntry Z)) Y :=
    (contDiffAt_fromProjectiveState 2 hD.ne').comp Y (contDiffAt_coreTailEntry 2 hk)
  exact contDiffAt_normalizedProjectiveWallMultiplier_two hc hτ hvalid.1.1.1.le
    (fun _ ht => (hvalid.2.1 _ ht).1) (fromProjectiveState_clock_pos hD)
    (hvalid.2.1 _ ⟨hvalid.1.1.1.le, le_rfl⟩).2 (if i = 0 then 0 else 2)

/-- The reflected finite tail has the exact multiplicative form used in B.45. -/
theorem coreTail_reflected_multiplier_state {η : ℝ} {Y : CoreAngleState} (hvalid : coreTailValid η Y) :
    projectiveReflection (coreTailState η Y) =
      ![-coreTailState η Y 0, Y 1 * coreTailMultiplier η Y 0, Y 2 * coreTailMultiplier η Y 1, η] := by
  ext i
  fin_cases i
  · rfl
  · exact coreTailMultiplier_formula hvalid 0
  · exact coreTailMultiplier_formula hvalid 1
  · exact coreTailState_active hvalid

end BianchiIX
