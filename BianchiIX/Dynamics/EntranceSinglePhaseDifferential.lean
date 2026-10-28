import BianchiIX.Dynamics.EntranceSinglePhaseCorrection
import BianchiIX.Dynamics.EntranceSignedRadialBounds

noncomputable section

namespace BianchiIX

theorem entranceSinglePhaseError_differential {y : ProjectiveState}
    (hm : 2 ≤ y 0) (hu : |y 1| ≤ 1 / 10000) (hw : |y 3| ≤ 1 / 10000) :
    ContDiffAt ℝ 2 entranceSinglePhaseError y ∧ ∀ d : ProjectiveState,
      fderiv ℝ entranceSinglePhaseError y d =
        fderiv ℝ stableStrongProjectionError (stableRestriction y) (stableRestriction d) +
        y 2 * d 2 / entranceStableRadius y -
        (y 2) ^ 2 * fderiv ℝ entranceStablePhase y d /
          (entranceStableRadius y * (entranceStableRadius y + entranceStablePhase y - 1)) := by
  have hu' : |y 1| < 1 / 200 := by linarith only [hu]
  have hw' : |y 3| < 1 / 200 := by linarith only [hw]
  have HE := (stableStrongProjectionError_differential (y := stableRestriction y) hm hu' hw').1
  have HP := contDiffAt_entranceStablePhase_two hm hu' hw'
  have HR := entranceStableRadius_signed_fderiv hm (by linarith only [hu]) (by linarith only [hw])
  have HQ : entranceSinglePhaseError = (fun z : ProjectiveState =>
      stableStrongProjectionError (stableRestriction z) + entranceStableRadius z -
        (entranceStablePhase z - 1)) := by
    funext z
    dsimp [entranceSinglePhaseError, stableStrongProjectionError, entranceStablePhase, stableRestriction]
    ring
  have Hreg := ((HE.comp y stableRestriction.contDiff.contDiffAt).add HR.1).sub (HP.sub (contDiffAt_const (c := (1 : ℝ))))
  change ContDiffAt ℝ 2 (fun z : ProjectiveState => stableStrongProjectionError (stableRestriction z) +
    entranceStableRadius z - (entranceStablePhase z - 1)) y at Hreg
  rw [← HQ] at Hreg
  refine ⟨Hreg, ?_⟩
  intro d
  have HD := (((HE.differentiableAt (by norm_num)).hasFDerivAt.comp y stableRestriction.hasFDerivAt).add
    (HR.1.differentiableAt (by norm_num)).hasFDerivAt).sub
      ((HP.differentiableAt (by norm_num)).hasFDerivAt.sub_const 1)
  change HasFDerivAt (fun z : ProjectiveState => stableStrongProjectionError (stableRestriction z) +
    entranceStableRadius z - (entranceStablePhase z - 1)) _ y at HD
  rw [← HQ] at HD
  rw [HD.fderiv]
  simp only [sub_apply, add_apply, ContinuousLinearMap.comp_apply]
  rw [HR.2]
  have hχ : 0 < entranceStablePhase y - 1 := sub_pos.mpr (entranceStablePhase_large_lower hm hu hw).2
  have hr : 0 < entranceStableRadius y := hχ.trans_le (phaseNorm_ge hχ.le)
  have hden : 0 < entranceStableRadius y + entranceStablePhase y - 1 := by linarith only [hr, hχ]
  have HS := entranceStableRadius_sq y
  field_simp [hr.ne', hden.ne']
  linear_combination -(fderiv ℝ entranceStablePhase y d) * HS

theorem entranceSinglePhaseError_radius_lower {α : ℝ} {y : ProjectiveState}
    (_hα : 0 < α) (hscale : 1 / α ≤ y 0 + 1)
    (hm : 2 ≤ y 0) (hu : |y 1| ≤ 1 / 10000) (hw : |y 3| ≤ 1 / 10000) :
    1 / (4 * α) ≤ entranceStableRadius y ∧
      1 / (4 * α) ≤ entranceStableRadius y + entranceStablePhase y - 1 := by
  have HP := entranceStablePhase_large_lower hm hu hw
  have HR : entranceStablePhase y - 1 ≤ entranceStableRadius y := phaseNorm_ge (sub_pos.mpr HP.2).le
  have Hscale : 1 / (4 * α) ≤ (y 0 + 1) / 4 := by
    calc
      _ = (1 / α) / 4 := by ring
      _ ≤ _ := div_le_div_of_nonneg_right hscale (by norm_num)
  exact ⟨Hscale.trans (HP.1.trans HR), Hscale.trans (HP.1.trans (by linarith only [HR, HP.2]))⟩

end BianchiIX
