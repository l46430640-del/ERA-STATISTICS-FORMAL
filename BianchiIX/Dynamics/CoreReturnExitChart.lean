import BianchiIX.Dynamics.CoreReturnEstimates
import BianchiIX.Dynamics.CoreTailMultipliers

noncomputable section

namespace BianchiIX

open Set

theorem coreRadiusReturnValid_denom_pos {Y : CoreAngleState} (H : coreRadiusReturnValid Y) :
    0 < projectiveStateDenom (coreRadiusEntry Y) := by
  have hzero := (H.2.1 0 ⟨le_rfl, H.1.1.1.le⟩).2
  rw [normalizedMaxCurve_initial] at hzero
  change 0 < 1 + (6 / projectiveStateDenom (coreRadiusEntry Y) - 1) at hzero
  by_contra! hn
  have HD := div_nonpos_of_nonneg_of_nonpos (by norm_num : (0 : ℝ) ≤ 6) hn
  linarith only [hzero, HD]

/-- A downward unit-wall crossing of radius at least two is on the negative phase branch. -/
theorem core_section_downward_phase {m u w : ℝ}
    (hr : 2 ≤ coreRadius m 1) (hu : 0 ≤ u ∧ u ≤ 1 / 4) (hw : 0 ≤ w ∧ w ≤ 1 / 4)
    (hvel : activeVelocity m u 1 w < 0) : m < 1 := by
  have hcoupling : coupling u 1 w ≤ 5 / 16 := by
    have H := mul_le_mul hu.2 (by linarith only [hw.2] : 1 + w ≤ 5 / 4)
      (by linarith only [hw.1] : 0 ≤ 1 + w) (by norm_num : (0 : ℝ) ≤ 1 / 4)
    dsimp [coupling]
    nlinarith only [H, sq_nonneg u]
  have hs : (2 : ℝ) ^ 2 ≤ coreRadius m 1 ^ 2 :=
    (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 2) (Real.sqrt_nonneg _)).mpr hr
  rw [coreRadius_sq] at hs
  dsimp only [coreEnergy] at hs
  change (m - 1 - coupling u 1 w) * 1 < 0 at hvel
  by_contra! hm
  have hm2 : m ≤ 2 := by linarith only [hvel, hcoupling]
  nlinarith only [hs, mul_nonneg (sub_nonneg.mpr hm) (sub_nonneg.mpr hm2)]

/-- The canonical core output is the actual initial state of its subsequent connection. -/
theorem coreRadiusReturn_exit_chart {Y : CoreAngleState} (H : coreRadiusReturnValid Y)
    (hr : 2 ≤ coreReturnState coreRadiusReturnTime Y 0)
    (hu : 0 ≤ coreReturnState coreRadiusReturnTime Y 1 ∧ coreReturnState coreRadiusReturnTime Y 1 ≤ 1 / 4)
    (hw : 0 ≤ coreReturnState coreRadiusReturnTime Y 2 ∧ coreReturnState coreRadiusReturnTime Y 2 ≤ 1 / 4) :
    coreTailEntry (coreReturnState coreRadiusReturnTime Y) =
      projectiveOriginalFlow (coreRadiusEntry Y) 0 (coreRadiusReturnTime Y) := by
  let x := fromProjectiveState (coreRadiusEntry Y)
  let T := coreRadiusReturnTime Y
  let y := projectiveOriginalFlow (coreRadiusEntry Y) 0 T
  have hD := coreRadiusReturnValid_denom_pos H
  have hc := fromProjectiveState_constraint hD.ne'
  have hT : 0 < T := H.1.1.1
  have hA : 0 < 1 + normalizedMaxCurve x 0 T 0 := (H.2.1 T ⟨hT.le, le_rfl⟩).2
  have hcT := (normalizedMaxCurve_forward_of_constraint hc hT.le).2.1
  have hv : y 2 = 1 := H.1.1.2.2
  have hn := H.2.2.2
  rw [normalizedEventRate, projectiveActiveWall_fderiv_field hA.ne' hcT] at hn
  have hvel : activeVelocity (y 0) (y 1) 1 (y 3) < 0 := by
    have HH : projectiveField y 2 < 0 := by
      by_contra! hh
      exact (not_le_of_gt hn) (mul_nonneg hA.le hh)
    change activeVelocity (y 0) (y 1) (y 2) (y 3) < 0 at HH
    rwa [hv] at HH
  have hw' : 0 ≤ y 3 ∧ y 3 ≤ 1 / 4 := by
    change 0 ≤ y 2 * y 3 ∧ y 2 * y 3 ≤ 1 / 4 at hw
    simpa only [hv, one_mul] using hw
  have hr' : 2 ≤ coreRadius (y 0) 1 := by
    change 2 ≤ coreRadius (y 0) (y 2) at hr
    rwa [hv] at hr
  exact coreTailEntry_of_exit (core_section_downward_phase hr' hu hw' hvel) hv

end BianchiIX
