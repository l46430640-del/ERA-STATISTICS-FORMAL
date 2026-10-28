import BianchiIX.Dynamics.CoreAngle

noncomputable section

namespace BianchiIX

def projectiveCoreAngle (y : ProjectiveState) : ℝ := coreAngle (y 0) (y 2)

/-- Angular speed in the original normalized Einstein time. -/
def coreOriginalClockRate (y : ProjectiveState) : ℝ :=
  (6 / projectiveStateDenom y) * coreRadius (y 0) (y 2) *
    coreClockFactor (coreRadius (y 0) (y 2)) (y 1) (y 3)

theorem contDiffAt_projectiveCoreAngle (n : WithTop ℕ∞) {y : ProjectiveState}
    (hv : 0 < y 2) : ContDiffAt ℝ n projectiveCoreAngle y := by
  have hv0 := ne_of_gt hv
  unfold projectiveCoreAngle coreAngle
  fun_prop

theorem contDiffAt_projectiveCoreRadius (n : WithTop ℕ∞) {y : ProjectiveState}
    (hv : 0 < y 2) : ContDiffAt ℝ n (fun z : ProjectiveState => coreRadius (z 0) (z 2)) y := by
  have he : coreEnergy (y 0) (y 2) ≠ 0 := by unfold coreEnergy; positivity
  have he' : (y 0 - 1) ^ 2 + y 2 ^ 2 ≠ 0 := he
  unfold coreRadius coreEnergy
  fun_prop

theorem contDiffAt_toCoreAngleState (n : WithTop ℕ∞) {y : ProjectiveState}
    (hv : 0 < y 2) : ContDiffAt ℝ n toCoreAngleState y := by
  have hr := contDiffAt_projectiveCoreRadius n hv
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i <;> dsimp [toCoreAngleState] <;> fun_prop

theorem contDiffAt_projectiveCoreClockFactor (n : WithTop ℕ∞) {y : ProjectiveState}
    (hv : 0 < y 2) :
    ContDiffAt ℝ n (fun z : ProjectiveState =>
      coreClockFactor (coreRadius (z 0) (z 2)) (z 1) (z 3)) y := by
  have hr := contDiffAt_projectiveCoreRadius n hv
  have hr2 : coreRadius (y 0) (y 2) ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt (coreRadius_pos hv))
  unfold coreClockFactor
  fun_prop

theorem contDiffAt_coreOriginalClockRate (n : WithTop ℕ∞) {y : ProjectiveState}
    (hv : 0 < y 2) (hD : projectiveStateDenom y ≠ 0) :
    ContDiffAt ℝ n coreOriginalClockRate y := by
  have hr := contDiffAt_projectiveCoreRadius n hv
  have hr2 : coreRadius (y 0) (y 2) ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt (coreRadius_pos hv))
  have hden := (contDiff_projectiveStateDenom n).contDiffAt (x := y)
  unfold coreOriginalClockRate coreClockFactor
  fun_prop

theorem projectiveCoreAngle_fderiv_field {y : ProjectiveState} (hv : 0 < y 2) :
    fderiv ℝ projectiveCoreAngle y (projectiveOriginalField y) = coreOriginalClockRate y := by
  let beta : ℝ → ProjectiveState := fun s => y + s • projectiveOriginalField y
  have hzero : beta 0 = y := by simp [beta]
  have hb : HasDerivAt beta (projectiveOriginalField (beta 0)) 0 := by
    convert! (hasDerivAt_const (0 : ℝ) y).add
      ((hasDerivAt_id (0 : ℝ)).smul_const (projectiveOriginalField y)) using 1
    simp [hzero]
  have hc := ((contDiffAt_projectiveCoreAngle 1 hv).differentiableAt (by norm_num)).hasFDerivAt
  have H := (hzero.symm ▸ hc).comp_hasDerivAt 0 hb
  have H' := hasDerivAt_coreAngle_scaled hb (by simpa only [hzero] using hv)
  simpa only [hzero, coreOriginalClockRate, projectiveCoreAngle] using H.unique H'

theorem toCoreAngleState_fderiv_field {y : ProjectiveState} (hv : 0 < y 2)
    (hd : coreClockFactor (coreRadius (y 0) (y 2)) (y 1) (y 3) ≠ 0) :
    fderiv ℝ toCoreAngleState y (projectiveOriginalField y) =
      coreOriginalClockRate y • coreAngleField (projectiveCoreAngle y) (toCoreAngleState y) := by
  let beta : ℝ → ProjectiveState := fun s => y + s • projectiveOriginalField y
  have hzero : beta 0 = y := by simp [beta]
  have hb : HasDerivAt beta (projectiveOriginalField (beta 0)) 0 := by
    convert! (hasDerivAt_const (0 : ℝ) y).add
      ((hasDerivAt_id (0 : ℝ)).smul_const (projectiveOriginalField y)) using 1
    simp [hzero]
  have hp := ((contDiffAt_toCoreAngleState 1 hv).differentiableAt (by norm_num)).hasFDerivAt
  have H := (hzero.symm ▸ hp).comp_hasDerivAt 0 hb
  have H' := hasDerivAt_toCoreAngleState_scaled hb
    (by simpa only [hzero] using hv) (by simpa only [hzero] using hd)
  simpa only [hzero, coreOriginalClockRate, projectiveCoreAngle] using H.unique H'

end BianchiIX
