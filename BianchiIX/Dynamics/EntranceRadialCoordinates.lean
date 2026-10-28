import BianchiIX.Dynamics.EntranceRadialCoordinateBounds

noncomputable section

namespace BianchiIX

def entranceRadialCoordinates (y : ProjectiveState) : ProjectiveState :=
  ![entranceStableRadius y, y 1, y 2, y 3]

def entranceRadialDifferential (y : ProjectiveState) : ProjectiveState →L[ℝ] ProjectiveState :=
  ContinuousLinearMap.pi ![fderiv ℝ entranceStableRadius y, ContinuousLinearMap.proj 1,
    ContinuousLinearMap.proj 2, ContinuousLinearMap.proj 3]

def entranceRadialInverseDifferential (y : ProjectiveState) : ProjectiveState →L[ℝ] ProjectiveState :=
  ContinuousLinearMap.pi ![
    (entranceStableRadius y / ((entranceStablePhase y - 1) * entranceStablePartial y 0)) • ContinuousLinearMap.proj 0 -
    (entranceStablePartial y 1 / entranceStablePartial y 0) • ContinuousLinearMap.proj 1 -
    (y 2 / ((entranceStablePhase y - 1) * entranceStablePartial y 0)) • ContinuousLinearMap.proj 2 -
    (entranceStablePartial y 3 / entranceStablePartial y 0) • ContinuousLinearMap.proj 3,
    ContinuousLinearMap.proj 1, ContinuousLinearMap.proj 2, ContinuousLinearMap.proj 3]

theorem entranceRadialDifferential_apply (y v : ProjectiveState) :
    entranceRadialDifferential y v = ![fderiv ℝ entranceStableRadius y v, v 1, v 2, v 3] := by
  ext i
  fin_cases i <;> rfl

theorem entranceRadialInverseDifferential_apply (y v : ProjectiveState) :
    entranceRadialInverseDifferential y v =
      ![entranceStableRadius y / ((entranceStablePhase y - 1) * entranceStablePartial y 0) * v 0 -
        entranceStablePartial y 1 / entranceStablePartial y 0 * v 1 -
        y 2 / ((entranceStablePhase y - 1) * entranceStablePartial y 0) * v 2 -
        entranceStablePartial y 3 / entranceStablePartial y 0 * v 3, v 1, v 2, v 3] := by
  ext i
  fin_cases i <;> rfl

theorem contDiffAt_entranceRadialCoordinates_two {y : ProjectiveState}
    (hm : 2 ≤ y 0) (hu : |y 1| < 1 / 200) (hw : |y 3| < 1 / 200) (hv : 0 < y 2) :
    ContDiffAt ℝ 2 entranceRadialCoordinates y := by
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i
  · exact contDiffAt_entranceStableRadius_two hm hu hw hv
  · dsimp [entranceRadialCoordinates]; fun_prop
  · dsimp [entranceRadialCoordinates]; fun_prop
  · dsimp [entranceRadialCoordinates]; fun_prop

theorem hasFDerivAt_entranceRadialCoordinates {y : ProjectiveState}
    (hm : 2 ≤ y 0) (hu : |y 1| < 1 / 200) (hw : |y 3| < 1 / 200) (hv : 0 < y 2) :
    HasFDerivAt entranceRadialCoordinates (entranceRadialDifferential y) y := by
  apply hasFDerivAt_pi.mpr
  intro i
  fin_cases i
  · exact ((contDiffAt_entranceStableRadius_two hm hu hw hv).differentiableAt (by norm_num)).hasFDerivAt
  · exact hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 4) y
  · exact hasFDerivAt_apply (𝕜 := ℝ) (2 : Fin 4) y
  · exact hasFDerivAt_apply (𝕜 := ℝ) (3 : Fin 4) y

theorem entranceRadialDifferential_formula {y : ProjectiveState}
    (hm : 2 ≤ y 0) (hu : |y 1| < 1 / 200) (hw : |y 3| < 1 / 200) (hv : 0 < y 2)
    (v : ProjectiveState) :
    entranceRadialDifferential y v =
      ![((entranceStablePhase y - 1) * (entranceStablePartial y 0 * v 0 +
        entranceStablePartial y 1 * v 1 + entranceStablePartial y 3 * v 3) + y 2 * v 2) /
        entranceStableRadius y, v 1, v 2, v 3] := by
  rw [entranceRadialDifferential_apply, entranceStableRadius_fderiv hm hu hw hv,
    entranceStablePhase_fderiv_coordinates hm hu hw]

/-- Both inverse identities hold for the explicit four-coordinate differential. -/
theorem entranceRadialDifferential_inverse {y : ProjectiveState}
    (hm : 2 ≤ y 0) (hu : |y 1| < 1 / 200) (hw : |y 3| < 1 / 200) (hv : 0 < y 2)
    (hchi : entranceStablePhase y - 1 ≠ 0) (hPM : entranceStablePartial y 0 ≠ 0) :
    Function.LeftInverse (entranceRadialInverseDifferential y) (entranceRadialDifferential y) ∧
      Function.RightInverse (entranceRadialInverseDifferential y) (entranceRadialDifferential y) := by
  have hr := (entranceStableRadius_pos hv).ne'
  constructor
  · intro v
    rw [entranceRadialDifferential_formula hm hu hw hv, entranceRadialInverseDifferential_apply]
    ext i
    fin_cases i
    · dsimp
      field_simp
      ring
    · rfl
    · rfl
    · rfl
  · intro v
    rw [entranceRadialDifferential_formula hm hu hw hv, entranceRadialInverseDifferential_apply]
    ext i
    fin_cases i
    · dsimp
      field_simp
      ring
    · rfl
    · rfl
    · rfl

end BianchiIX
