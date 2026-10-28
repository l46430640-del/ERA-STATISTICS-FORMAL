import BianchiIX.Dynamics.CoreEntryDifferential
import BianchiIX.Dynamics.ConnectionPhysicalReturn
import BianchiIX.Dynamics.ProjectiveReflection

noncomputable section

namespace BianchiIX

def coreExitConnectionParameters (Z : CoreAngleState) : ConnectionParameters :=
  ![Real.sqrt (Z 0 ^ 2 - 1) - 1, Z 1, Z 2]

theorem coreExitConnectionParameters_phase {Z : CoreAngleState} (hK : 1 < Z 0) :
    phaseNorm (coreExitConnectionParameters Z 0 + 1) 1 = Z 0 := by
  have hs := Real.sq_sqrt (by nlinarith only [hK] : 0 ≤ Z 0 ^ 2 - 1)
  change Real.sqrt ((Real.sqrt (Z 0 ^ 2 - 1) - 1 + 1) ^ 2 + 1 ^ 2) = Z 0
  rw [show (Real.sqrt (Z 0 ^ 2 - 1) - 1 + 1) ^ 2 + 1 ^ 2 = Z 0 ^ 2 by nlinarith only [hs]]
  exact Real.sqrt_sq (by linarith only [hK])

theorem contDiffAt_coreExitConnectionParameters (n : WithTop ℕ∞) {Z : CoreAngleState} (hK : 1 < Z 0) :
    ContDiffAt ℝ n coreExitConnectionParameters Z := by
  have hs : Z 0 ^ 2 - 1 ≠ 0 := ne_of_gt (by nlinarith only [hK] : 0 < Z 0 ^ 2 - 1)
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i <;> dsimp [coreExitConnectionParameters] <;> fun_prop

theorem coreExitConnectionParameters_of_exit {y : ProjectiveState} (hM : y 0 < 1) (hV : y 2 = 1) :
    coreExitConnectionParameters (toCoreAngleState y) = ![-y 0, y 1, y 3] := by
  have hs : (toCoreAngleState y 0) ^ 2 - 1 = (y 0 - 1) ^ 2 := by
    change coreRadius (y 0) (y 2) ^ 2 - 1 = _
    rw [coreRadius_sq, hV]
    dsimp [coreEnergy]
    ring
  ext i
  fin_cases i
  · change Real.sqrt ((toCoreAngleState y 0) ^ 2 - 1) - 1 = -y 0
    rw [hs, Real.sqrt_sq_eq_abs, abs_of_neg (by linarith only [hM] : y 0 - 1 < 0)]
    ring
  · rfl
  · change y 2 * y 3 = y 3
    rw [hV, one_mul]

theorem coreRadiusEntry_reflected_exit {y : ProjectiveState} (hM : 1 < -y 0) (hW : y 3 = 1) :
    coreRadiusEntry ![phaseNorm (-y 0 - 1) 1, y 1, y 2] = projectiveReflection y := by
  have hs : phaseNorm (-y 0 - 1) 1 ^ 2 - 1 = (-y 0 - 1) ^ 2 := by
    rw [phaseNorm_sq]
    ring
  ext i
  fin_cases i
  · change 1 + Real.sqrt (phaseNorm (-y 0 - 1) 1 ^ 2 - 1) = -y 0
    rw [hs, Real.sqrt_sq (by linarith only [hM])]
    ring
  · rfl
  · exact hW.symm
  · rfl

end BianchiIX
