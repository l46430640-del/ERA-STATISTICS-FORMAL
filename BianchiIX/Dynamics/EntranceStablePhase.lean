import BianchiIX.Dynamics.StableProjectionSecondRegularity
import BianchiIX.Algebra.CoreAngle

noncomputable section

namespace BianchiIX

def entranceStablePhase (y : ProjectiveState) : ℝ :=
  stableBoundaryProjection (y 0) (y 1) (y 3)

def entranceStablePartial (y : ProjectiveState) (i : Fin 4) : ℝ :=
  fderiv ℝ entranceStablePhase y (Pi.single i 1)

def entranceStableRadius (y : ProjectiveState) : ℝ := coreRadius (entranceStablePhase y) (y 2)

theorem contDiffAt_entranceStablePhase_two {y : ProjectiveState}
    (hm : 2 ≤ y 0) (hu : |y 1| < 1 / 200) (hw : |y 3| < 1 / 200) :
    ContDiffAt ℝ 2 entranceStablePhase y :=
  (contDiffAt_stableBoundaryProjection_two (y := stableRestriction y) hm hu hw).comp y
    stableRestriction.contDiff.contDiffAt

theorem entranceStablePhase_fderiv {y : ProjectiveState}
    (hm : 2 ≤ y 0) (hu : |y 1| < 1 / 200) (hw : |y 3| < 1 / 200) (v : ProjectiveState) :
    fderiv ℝ entranceStablePhase y v =
      fderiv ℝ (fun z : StableState => stableBoundaryProjection (z 0) (z 1) (z 2))
        (stableRestriction y) (stableRestriction v) := by
  have H := ((contDiffAt_stableBoundaryProjection_two (y := stableRestriction y) hm hu hw).differentiableAt
    (by norm_num)).hasFDerivAt.comp y stableRestriction.hasFDerivAt
  exact congrArg (fun L : ProjectiveState →L[ℝ] ℝ => L v) H.fderiv

theorem entranceStablePartial_active {y : ProjectiveState}
    (hm : 2 ≤ y 0) (hu : |y 1| < 1 / 200) (hw : |y 3| < 1 / 200) :
    entranceStablePartial y 2 = 0 := by
  rw [entranceStablePartial, entranceStablePhase_fderiv hm hu hw]
  have hz : stableRestriction (Pi.single (2 : Fin 4) (1 : ℝ)) = 0 := by
    ext i
    fin_cases i <;> simp [stableRestriction]
  rw [hz, map_zero]

private theorem linearForm_four_coordinates (L : ProjectiveState →L[ℝ] ℝ) (v : ProjectiveState) :
    L v = L (Pi.single 0 1) * v 0 + L (Pi.single 1 1) * v 1 +
      L (Pi.single 2 1) * v 2 + L (Pi.single 3 1) * v 3 := by
  have heq : v = v 0 • Pi.single 0 1 + v 1 • Pi.single 1 1 +
      v 2 • Pi.single 2 1 + v 3 • Pi.single 3 1 := by
    ext i
    fin_cases i <;> simp
  conv_lhs => rw [heq]
  simp only [map_add, map_smul, smul_eq_mul]
  ring

theorem entranceStablePhase_fderiv_coordinates {y : ProjectiveState}
    (hm : 2 ≤ y 0) (hu : |y 1| < 1 / 200) (hw : |y 3| < 1 / 200) (v : ProjectiveState) :
    fderiv ℝ entranceStablePhase y v = entranceStablePartial y 0 * v 0 +
      entranceStablePartial y 1 * v 1 + entranceStablePartial y 3 * v 3 := by
  have H := linearForm_four_coordinates (fderiv ℝ entranceStablePhase y) v
  change _ = entranceStablePartial y 0 * v 0 + entranceStablePartial y 1 * v 1 +
    entranceStablePartial y 2 * v 2 + entranceStablePartial y 3 * v 3 at H
  simpa only [entranceStablePartial_active hm hu hw, zero_mul, add_zero] using H

/-- Stable-boundary invariance removes every term without an active wall. -/
theorem entranceStablePhase_fderiv_field {y : ProjectiveState}
    (hm : 2 ≤ y 0) (hu : |y 1| < 1 / 200) (hw : |y 3| < 1 / 200) :
    fderiv ℝ entranceStablePhase y (projectiveField y) =
      y 1 * y 2 * ((1 - y 0) * entranceStablePartial y 0 +
        y 3 * (entranceStablePartial y 1 - entranceStablePartial y 3)) -
      y 2 ^ 2 * (entranceStablePartial y 0 + y 1 / 2 * entranceStablePartial y 1) := by
  have hzero : fderiv ℝ entranceStablePhase y
      (stableInclusion (stableBoundaryField (stableRestriction y))) = 0 := by
    rw [entranceStablePhase_fderiv hm hu hw, stableRestriction_inclusion]
    exact stableBoundaryProjection_annihilates_field (y := stableRestriction y) hm hu hw
  rw [entranceStablePhase_fderiv_coordinates hm hu hw] at hzero ⊢
  simp [stableInclusion_apply, stableRestriction_apply, stableBoundaryField] at hzero
  dsimp [projectiveField, phaseVelocity, strongVelocity, weakVelocity, coupling,
    stableStrongRate, stableWeakRate] at hzero ⊢
  linear_combination hzero

theorem entranceStableRadius_pos {y : ProjectiveState} (hv : 0 < y 2) :
    0 < entranceStableRadius y := coreRadius_pos hv

theorem entranceStableRadius_sq (y : ProjectiveState) :
    entranceStableRadius y ^ 2 = (entranceStablePhase y - 1) ^ 2 + y 2 ^ 2 :=
  coreRadius_sq _ _

theorem contDiffAt_entranceStableRadius_two {y : ProjectiveState}
    (hm : 2 ≤ y 0) (hu : |y 1| < 1 / 200) (hw : |y 3| < 1 / 200) (hv : 0 < y 2) :
    ContDiffAt ℝ 2 entranceStableRadius y := by
  have hP := contDiffAt_entranceStablePhase_two hm hu hw
  have hV : ContDiffAt ℝ 2 (fun z : ProjectiveState => z 2) y := by fun_prop
  exact (((hP.sub contDiffAt_const).pow 2).add (hV.pow 2)).sqrt (by positivity)

theorem entranceStableRadius_fderiv {y : ProjectiveState}
    (hm : 2 ≤ y 0) (hu : |y 1| < 1 / 200) (hw : |y 3| < 1 / 200) (hv : 0 < y 2)
    (v : ProjectiveState) :
    fderiv ℝ entranceStableRadius y v =
      ((entranceStablePhase y - 1) * fderiv ℝ entranceStablePhase y v + y 2 * v 2) /
        entranceStableRadius y := by
  have hP := (contDiffAt_entranceStablePhase_two hm hu hw).differentiableAt (by norm_num)
  have H := (((hP.hasFDerivAt.sub_const 1).pow 2).add
    ((hasFDerivAt_apply (𝕜 := ℝ) (2 : Fin 4) y).pow 2)).sqrt
      (by change (entranceStablePhase y - 1) ^ 2 + y 2 ^ 2 ≠ 0; positivity)
  change HasFDerivAt entranceStableRadius _ y at H
  rw [H.fderiv]
  simp only [Pi.add_apply, smul_apply, add_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
  change _ = _ / Real.sqrt ((entranceStablePhase y - 1) ^ 2 + y 2 ^ 2)
  ring

end BianchiIX
