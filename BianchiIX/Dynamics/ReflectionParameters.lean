import BianchiIX.Dynamics.ReflectionReturn
import BianchiIX.Dynamics.CoreConnectionDifferential

noncomputable section

namespace BianchiIX

/-- The ordinary coordinate change sends a unit radial vector to a unit physical-phase vector. -/
theorem coreExitConnectionParameters_unit_phase {Y v : CoreAngleState} (hR : 1 < Y 0) (hv : v 0 = 1) :
    let p := coreExitConnectionParameters Y
    let w := fderiv ℝ coreExitConnectionParameters Y v
    ((p 0 + 1) / phaseNorm (p 0 + 1) 1) * w 0 = 1 ∧ w 1 = v 1 ∧ w 2 = v 2 := by
  simpa only [hv] using coreExitConnectionParameters_differential hR v

/-- The long-connection chart is comparable to the physical core radius on the overlap. -/
theorem coreExitConnectionParameters_long_range {Y : CoreAngleState} (hR : 11 / 2 ≤ Y 0) :
    4 ≤ coreExitConnectionParameters Y 0 ∧ Y 0 / 2 ≤ coreExitConnectionParameters Y 0 ∧
      coreExitConnectionParameters Y 0 < Y 0 := by
  have hsq := Real.sq_sqrt (by nlinarith only [hR] : 0 ≤ Y 0 ^ 2 - 1)
  have hs := Real.sqrt_nonneg (Y 0 ^ 2 - 1)
  change 4 ≤ Real.sqrt (Y 0 ^ 2 - 1) - 1 ∧ Y 0 / 2 ≤ Real.sqrt (Y 0 ^ 2 - 1) - 1 ∧
    Real.sqrt (Y 0 ^ 2 - 1) - 1 < Y 0
  refine ⟨?_, ?_, ?_⟩
  · nlinarith only [hsq, hs, hR, sq_nonneg (Y 0 - 11 / 2)]
  · have hnear : Y 0 - 1 ≤ Real.sqrt (Y 0 ^ 2 - 1) := by nlinarith only [hsq, hs, hR]
    linarith only [hnear, hR]
  · nlinarith only [hsq, hs, hR]

end BianchiIX
