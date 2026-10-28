import BianchiIX.Algebra.CoreAngle
import BianchiIX.Dynamics.ProjectiveOriginalTime

noncomputable section

namespace BianchiIX

abbrev CoreAngleState := Fin 3 → ℝ

def toCoreAngleState (y : ProjectiveState) : CoreAngleState :=
  ![coreRadius (y 0) (y 2), y 1, y 2 * y 3]

def fromCoreAngleState (z : ℝ) (y : CoreAngleState) : ProjectiveState :=
  let v := y 0 / Real.cosh z
  ![1 - y 0 * Real.tanh z, y 1, v, y 2 / v]

/-- The exact nonautonomous system (A.8), with the angle itself as time. -/
def coreAngleField (z : ℝ) (y : CoreAngleState) : CoreAngleState :=
  let r := y 0
  let u := y 1
  let p := y 2
  let v := r / Real.cosh z
  let w := p / v
  let d := coreClockFactor r u w
  ![(-coupling u v w - Real.tanh z * (u - w) ^ 2 / r) / d,
    u * (-r / 2 + Real.tanh z + w / Real.cosh z + (u ^ 2 - w ^ 2) / (2 * r)) / d,
    -2 * p * (1 + coupling u v w) / (r * d)]

theorem fromCoreAngleState_toCoreAngleState {y : ProjectiveState} (hv : 0 < y 2) :
    fromCoreAngleState (coreAngle (y 0) (y 2)) (toCoreAngleState y) = y := by
  ext i
  fin_cases i
  · exact (coreAngle_coordinates hv).2
  · rfl
  · exact (coreAngle_coordinates hv).1
  · change y 2 * y 3 / (coreRadius (y 0) (y 2) / Real.cosh (coreAngle (y 0) (y 2))) = y 3
    rw [(coreAngle_coordinates hv).1]
    field_simp

theorem coreAngleField_coordinates {m u v w : ℝ} (hv : 0 < v) :
    coreAngleField (coreAngle m v) ![coreRadius m v, u, v * w] =
      ![(-coupling u v w + (m - 1) * (u - w) ^ 2 / coreRadius m v ^ 2) /
          coreClockFactor (coreRadius m v) u w,
        strongVelocity m u v w / (coreRadius m v * coreClockFactor (coreRadius m v) u w),
        -2 * (v * w) * (1 + coupling u v w) /
          (coreRadius m v * coreClockFactor (coreRadius m v) u w)] := by
  have hr := ne_of_gt (coreRadius_pos (m := m) hv)
  have hv0 := ne_of_gt hv
  dsimp [coreAngleField]
  rw [(coreAngle_coordinates hv).1, mul_div_cancel_left₀ _ hv0, tanh_coreAngle hv, cosh_coreAngle hv]
  ext i
  fin_cases i
  · dsimp
    congr 1
    field_simp
    ring
  · dsimp
    rw [← div_div (strongVelocity m u v w) (coreRadius m v) (coreClockFactor (coreRadius m v) u w)]
    congr 1
    field_simp
    rw [coreRadius_sq]
    unfold coreEnergy strongVelocity
    ring
  · rfl

/-- A common scalar time factor is retained, so this also applies in original Einstein time. -/
theorem hasDerivAt_coreAngle_scaled {β : ℝ → ProjectiveState} {a t : ℝ}
    (hβ : HasDerivAt β (a • projectiveField (β t)) t) (hv : 0 < β t 2) :
    HasDerivAt (fun s => coreAngle (β s 0) (β s 2))
      (a * coreRadius (β t 0) (β t 2) * coreClockFactor (coreRadius (β t 0) (β t 2)) (β t 1) (β t 3)) t := by
  have hm := hasDerivAt_pi.mp hβ 0
  have hV := hasDerivAt_pi.mp hβ 2
  have H := hasDerivAt_coreAngle hm hV hv
  convert! H using 1
  simp only [Pi.smul_apply, smul_eq_mul]
  change _ = ((β t 0 - 1) * (a * activeVelocity (β t 0) (β t 1) (β t 2) (β t 3)) -
    β t 2 * (a * phaseVelocity (β t 0) (β t 1) (β t 2) (β t 3))) /
      (coreRadius (β t 0) (β t 2) * β t 2)
  rw [show ((β t 0 - 1) * (a * activeVelocity (β t 0) (β t 1) (β t 2) (β t 3)) -
    β t 2 * (a * phaseVelocity (β t 0) (β t 1) (β t 2) (β t 3))) /
      (coreRadius (β t 0) (β t 2) * β t 2) =
    a * (((β t 0 - 1) * activeVelocity (β t 0) (β t 1) (β t 2) (β t 3) -
    β t 2 * phaseVelocity (β t 0) (β t 1) (β t 2) (β t 3)) /
      (coreRadius (β t 0) (β t 2) * β t 2)) by ring]
  rw [coreAngle_directional hv]
  ring

theorem hasDerivAt_toCoreAngleState_scaled {β : ℝ → ProjectiveState} {a t : ℝ}
    (hβ : HasDerivAt β (a • projectiveField (β t)) t) (hv : 0 < β t 2)
    (hd : coreClockFactor (coreRadius (β t 0) (β t 2)) (β t 1) (β t 3) ≠ 0) :
    HasDerivAt (fun s => toCoreAngleState (β s))
      ((a * coreRadius (β t 0) (β t 2) * coreClockFactor (coreRadius (β t 0) (β t 2)) (β t 1) (β t 3)) •
        coreAngleField (coreAngle (β t 0) (β t 2)) (toCoreAngleState (β t))) t := by
  have hr := ne_of_gt (coreRadius_pos (m := β t 0) hv)
  have hm := hasDerivAt_pi.mp hβ 0
  have hu := hasDerivAt_pi.mp hβ 1
  have hV := hasDerivAt_pi.mp hβ 2
  have hw := hasDerivAt_pi.mp hβ 3
  rw [show toCoreAngleState (β t) = ![coreRadius (β t 0) (β t 2), β t 1, β t 2 * β t 3] from rfl,
    coreAngleField_coordinates hv]
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · convert! hasDerivAt_coreRadius hm hV hv using 1
    simp only [Pi.smul_apply, smul_eq_mul]
    change _ = ((β t 0 - 1) * (a * phaseVelocity (β t 0) (β t 1) (β t 2) (β t 3)) +
      β t 2 * (a * activeVelocity (β t 0) (β t 1) (β t 2) (β t 3))) / coreRadius (β t 0) (β t 2)
    rw [show ((β t 0 - 1) * (a * phaseVelocity (β t 0) (β t 1) (β t 2) (β t 3)) +
      β t 2 * (a * activeVelocity (β t 0) (β t 1) (β t 2) (β t 3))) / coreRadius (β t 0) (β t 2) =
      a * (((β t 0 - 1) * phaseVelocity (β t 0) (β t 1) (β t 2) (β t 3) +
      β t 2 * activeVelocity (β t 0) (β t 1) (β t 2) (β t 3)) / coreRadius (β t 0) (β t 2)) by ring]
    rw [coreRadius_directional hv]
    dsimp
    field_simp
  · convert! hu using 1
    change _ = a * strongVelocity (β t 0) (β t 1) (β t 2) (β t 3)
    dsimp
    field_simp
  · convert! hV.mul hw using 1
    simp only [Pi.smul_apply, smul_eq_mul]
    change _ = a * activeVelocity (β t 0) (β t 1) (β t 2) (β t 3) * β t 3 +
      β t 2 * (a * weakVelocity (β t 0) (β t 1) (β t 2) (β t 3))
    rw [show a * activeVelocity (β t 0) (β t 1) (β t 2) (β t 3) * β t 3 +
      β t 2 * (a * weakVelocity (β t 0) (β t 1) (β t 2) (β t 3)) =
      a * (activeVelocity (β t 0) (β t 1) (β t 2) (β t 3) * β t 3 +
      β t 2 * weakVelocity (β t 0) (β t 1) (β t 2) (β t 3)) by ring]
    rw [weak_product_directional]
    dsimp
    field_simp

end BianchiIX
