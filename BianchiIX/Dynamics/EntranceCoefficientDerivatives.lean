import BianchiIX.Dynamics.EntranceRadialCoefficients

noncomputable section

namespace BianchiIX

local instance entranceCoefficientOperatorGroup : NormedAddCommGroup (ProjectiveState →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance entranceCoefficientOperatorSpace : NormedSpace ℝ (ProjectiveState →L[ℝ] ℝ) := inferInstance

def entranceStrongBracket (y : ProjectiveState) : ℝ :=
  entranceStablePhase y - 1 - (y 0 - 1) * entranceStablePartial y 0

theorem contDiffAt_entranceStablePartial_one {y : ProjectiveState}
    (hm : 2 ≤ y 0) (hu : |y 1| < 1 / 200) (hw : |y 3| < 1 / 200) (i : Fin 4) :
    ContDiffAt ℝ 1 (fun z => entranceStablePartial z i) y :=
  ((contDiffAt_entranceStablePhase_two hm hu hw).fderiv_right
    (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).clm_apply contDiffAt_const

theorem entranceStablePartial_fderiv {y : ProjectiveState}
    (hm : 2 ≤ y 0) (hu : |y 1| < 1 / 200) (hw : |y 3| < 1 / 200)
    (i : Fin 4) (v : ProjectiveState) :
    fderiv ℝ (fun z => entranceStablePartial z i) y v =
      fderiv ℝ (fderiv ℝ entranceStablePhase) y v (Pi.single i 1) := by
  have H := (((contDiffAt_entranceStablePhase_two hm hu hw).fderiv_right
    (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiableAt (by norm_num)).hasFDerivAt.clm_apply
      (hasFDerivAt_const (𝕜 := ℝ) (Pi.single i (1 : ℝ)) y)
  exact congrArg (fun L : ProjectiveState →L[ℝ] ℝ => L v) H.fderiv |>.trans (by simp)

theorem contDiffAt_entranceWeakNumerator_one {y : ProjectiveState}
    (hm : 2 ≤ y 0) (hu : |y 1| < 1 / 200) (hw : |y 3| < 1 / 200) :
    ContDiffAt ℝ 1 entranceWeakNumerator y := by
  have hP := (contDiffAt_entranceStablePhase_two hm hu hw).of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  have hPM := contDiffAt_entranceStablePartial_one hm hu hw 0
  unfold entranceWeakNumerator
  fun_prop

theorem entranceWeakNumerator_fderiv {y : ProjectiveState}
    (hm : 2 ≤ y 0) (hu : |y 1| < 1 / 200) (hw : |y 3| < 1 / 200) (v : ProjectiveState) :
    fderiv ℝ entranceWeakNumerator y v = v 0 + (2 * y 1 - y 3) * v 1 - y 1 * v 3 -
      entranceStablePartial y 0 * fderiv ℝ entranceStablePhase y v -
      (entranceStablePhase y - 1) * fderiv ℝ (fderiv ℝ entranceStablePhase) y v (Pi.single 0 1) := by
  have hP := (contDiffAt_entranceStablePhase_two hm hu hw).differentiableAt (by norm_num)
  have hPM := (contDiffAt_entranceStablePartial_one hm hu hw 0).differentiableAt (by norm_num)
  have hd (i : Fin 4) := hasFDerivAt_apply (𝕜 := ℝ) i y
  have H := (((hd 0).sub_const 1).sub ((hd 1).mul ((hd 3).sub (hd 1)))).sub
    ((hP.hasFDerivAt.sub_const 1).mul hPM.hasFDerivAt)
  change HasFDerivAt entranceWeakNumerator _ y at H
  rw [H.fderiv]
  simp only [Pi.sub_apply, sub_apply, add_apply, smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
  rw [entranceStablePartial_fderiv hm hu hw]
  ring

/-- The three ordinary derivative columns in (C.19) use only the Hessian of P. -/
theorem entranceWeakNumerator_partials {y : ProjectiveState}
    (hm : 2 ≤ y 0) (hu : |y 1| < 1 / 200) (hw : |y 3| < 1 / 200) :
    fderiv ℝ entranceWeakNumerator y (Pi.single 0 1) =
      1 - entranceStablePartial y 0 ^ 2 - (entranceStablePhase y - 1) *
        fderiv ℝ (fderiv ℝ entranceStablePhase) y (Pi.single 0 1) (Pi.single 0 1) ∧
    fderiv ℝ entranceWeakNumerator y (Pi.single 1 1) =
      2 * y 1 - y 3 - entranceStablePartial y 0 * entranceStablePartial y 1 - (entranceStablePhase y - 1) *
        fderiv ℝ (fderiv ℝ entranceStablePhase) y (Pi.single 1 1) (Pi.single 0 1) ∧
    fderiv ℝ entranceWeakNumerator y (Pi.single 3 1) =
      -y 1 - entranceStablePartial y 0 * entranceStablePartial y 3 - (entranceStablePhase y - 1) *
        fderiv ℝ (fderiv ℝ entranceStablePhase) y (Pi.single 3 1) (Pi.single 0 1) := by
  simp only [entranceWeakNumerator_fderiv hm hu hw]
  simp [entranceStablePartial, sq]

theorem entranceStrongBracket_eq (y : ProjectiveState) :
    entranceStrongBracket y = (entranceStablePhase y - y 0) -
      (y 0 - 1) * (entranceStablePartial y 0 - 1) := by
  unfold entranceStrongBracket
  ring

theorem entranceStrongRemainder_bracket (y : ProjectiveState) :
    entranceStrongRemainder y = (entranceStablePhase y - 1) * entranceStrongBracket y +
      (entranceStablePhase y - 1) * y 3 * (entranceStablePartial y 1 - entranceStablePartial y 3) -
      (1 / 2) * (entranceStablePhase y - 1) * y 2 * entranceStablePartial y 1 := by
  rw [entranceStrongBracket_eq]
  rfl

theorem entranceStrongBracket_fderiv {y : ProjectiveState}
    (hm : 2 ≤ y 0) (hu : |y 1| < 1 / 200) (hw : |y 3| < 1 / 200) (v : ProjectiveState) :
    fderiv ℝ entranceStrongBracket y v = fderiv ℝ entranceStablePhase y v -
      v 0 * entranceStablePartial y 0 - (y 0 - 1) *
        fderiv ℝ (fderiv ℝ entranceStablePhase) y v (Pi.single 0 1) := by
  have hP := (contDiffAt_entranceStablePhase_two hm hu hw).differentiableAt (by norm_num)
  have hPM := (contDiffAt_entranceStablePartial_one hm hu hw 0).differentiableAt (by norm_num)
  have H := (hP.hasFDerivAt.sub_const 1).sub
    (((hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 4) y).sub_const 1).mul hPM.hasFDerivAt)
  change HasFDerivAt entranceStrongBracket _ y at H
  rw [H.fderiv]
  simp only [sub_apply, add_apply, smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
  rw [entranceStablePartial_fderiv hm hu hw]
  ring

theorem entranceStrongBracket_phase_cancellation {y : ProjectiveState}
    (hm : 2 ≤ y 0) (hu : |y 1| < 1 / 200) (hw : |y 3| < 1 / 200) :
    fderiv ℝ entranceStrongBracket y (Pi.single 0 1) = -(y 0 - 1) *
      fderiv ℝ (fderiv ℝ entranceStablePhase) y (Pi.single 0 1) (Pi.single 0 1) := by
  rw [entranceStrongBracket_fderiv hm hu hw]
  simp only [entranceStablePartial, Pi.single_eq_same, one_mul, sub_self, zero_sub]
  ring

theorem contDiffAt_entranceRadialCoefficients_one {y : ProjectiveState}
    (hm : 2 ≤ y 0) (hu : |y 1| < 1 / 200) (hw : |y 3| < 1 / 200)
    (hv : 0 < y 2) (hD : entranceClockRate y ≠ 0) :
    ContDiffAt ℝ 1 entranceRadialStrongCoefficient y ∧
      ContDiffAt ℝ 1 entranceRadialWeakCoefficient y := by
  have hP := (contDiffAt_entranceStablePhase_two hm hu hw).of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  have hpartial := contDiffAt_entranceStablePartial_one hm hu hw
  have hr := (contDiffAt_entranceStableRadius_two hm hu hw hv).of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  have hclock : ContDiffAt ℝ 1 entranceClockRate y := by
    unfold entranceClockRate connectionSpeed coupling
    fun_prop
  have hden := mul_ne_zero (entranceStableRadius_pos hv).ne' hD
  constructor
  · unfold entranceRadialStrongCoefficient
    apply ContDiffAt.div _ (hr.mul hclock) hden
    fun_prop
  · exact (contDiffAt_entranceWeakNumerator_one hm hu hw).div (hr.mul hclock) hden

end BianchiIX
