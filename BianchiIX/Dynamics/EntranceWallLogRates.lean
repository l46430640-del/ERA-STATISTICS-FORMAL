import BianchiIX.Analysis.ConnectionAmplitudeDifferential
import BianchiIX.Dynamics.EntranceOperatorBounds

noncomputable section

namespace BianchiIX

def entranceStrongLogRate (y : ProjectiveState) : ℝ := connectionStrongClockRate (y 0) (y 1) (y 2) (y 3)

def entranceWeakLogRate (y : ProjectiveState) : ℝ := connectionWeakClockRate (y 0) (y 1) (y 2) (y 3)

theorem entranceWallLogRates_field {y : ProjectiveState} (hD : entranceClockRate y ≠ 0) :
    projectiveField y 1 = entranceClockRate y * entranceStrongLogRate y * y 1 ∧
      projectiveField y 3 = entranceClockRate y * entranceWeakLogRate y * y 3 := by
  have hn : connectionSpeed (y 0) (y 1) (y 2) (y 3) ≠ 0 := hD
  constructor
  · change strongVelocity _ _ _ _ = _
    unfold entranceClockRate entranceStrongLogRate connectionStrongClockRate strongVelocity connectionStrongRate
    field_simp
  · change weakVelocity _ _ _ _ = _
    unfold entranceClockRate entranceWeakLogRate connectionWeakClockRate weakVelocity
    field_simp
    unfold connectionSpeed
    ring

theorem hasDerivAt_entranceLogWalls_scaled {Y : ℝ → ProjectiveState} {a t : ℝ}
    (hY : HasDerivAt Y (a • projectiveField (Y t)) t)
    (hu : Y t 1 ≠ 0) (hw : Y t 3 ≠ 0) (hD : entranceClockRate (Y t) ≠ 0) :
    HasDerivAt (fun s => Real.log (Y s 1)) (a * entranceClockRate (Y t) * entranceStrongLogRate (Y t)) t ∧
      HasDerivAt (fun s => Real.log (Y s 3)) (a * entranceClockRate (Y t) * entranceWeakLogRate (Y t)) t := by
  obtain ⟨hs, hw'⟩ := entranceWallLogRates_field hD
  constructor
  · convert! (hasDerivAt_pi.mp hY 1).log hu using 1
    simp only [Pi.smul_apply, smul_eq_mul, hs]
    field_simp
  · convert! (hasDerivAt_pi.mp hY 3).log hw using 1
    simp only [Pi.smul_apply, smul_eq_mul, hw']
    field_simp

theorem contDiffAt_entranceWallLogRates (n : WithTop ℕ∞) {y : ProjectiveState}
    (hD : entranceClockRate y ≠ 0) :
    ContDiffAt ℝ n entranceStrongLogRate y ∧ ContDiffAt ℝ n entranceWeakLogRate y := by
  unfold entranceClockRate connectionSpeed coupling at hD
  constructor
  · unfold entranceStrongLogRate connectionStrongClockRate connectionStrongRate connectionSpeed coupling
    fun_prop (disch := assumption)
  · unfold entranceWeakLogRate connectionWeakClockRate connectionSpeed coupling
    fun_prop (disch := assumption)

theorem entranceWallLogRates_fderiv {y : ProjectiveState}
    (hD : entranceClockRate y ≠ 0) (v : ProjectiveState) :
    fderiv ℝ entranceStrongLogRate y v =
      (-y 0 * v 0 - (y 2 - y 3) * (v 2 - v 3) + y 1 * v 1 -
        entranceStrongLogRate y * (v 0 - (v 1 * (y 2 + y 3 - 2 * y 1) + y 1 * (v 2 + v 3)))) / entranceClockRate y ∧
      fderiv ℝ entranceWeakLogRate y v =
        (2 * (1 + coupling (y 1) (y 2) (y 3)) * v 0 -
          2 * y 0 * (v 1 * (y 2 + y 3 - 2 * y 1) + y 1 * (v 2 + v 3))) / entranceClockRate y ^ 2 := by
  have hl : HasDerivAt (fun t : ℝ => y + t • v) v 0 := by
    convert! (hasDerivAt_const (0 : ℝ) y).add ((hasDerivAt_id (0 : ℝ)).smul_const v) using 1
    simp
  have hd (i : Fin 4) := hasDerivAt_pi.mp hl i
  obtain ⟨hs, hw⟩ := contDiffAt_entranceWallLogRates 1 hD
  have hs' : HasFDerivAt entranceStrongLogRate (fderiv ℝ entranceStrongLogRate y) (y + (0 : ℝ) • v) := by
    simpa using (hs.differentiableAt (by norm_num)).hasFDerivAt
  have hw' : HasFDerivAt entranceWeakLogRate (fderiv ℝ entranceWeakLogRate y) (y + (0 : ℝ) • v) := by
    simpa using (hw.differentiableAt (by norm_num)).hasFDerivAt
  have hsCurve := hasDerivAt_connectionStrongClockRate (hd 0) (hd 1) (hd 2) (hd 3) (by simpa [entranceClockRate] using hD)
  have hwCurve := hasDerivAt_connectionWeakClockRate (hd 0) (hd 1) (hd 2) (hd 3) (by simpa [entranceClockRate] using hD)
  have hsf := hs'.comp_hasDerivAt 0 hl
  have hwf := hw'.comp_hasDerivAt 0 hl
  change HasDerivAt (fun s => connectionStrongClockRate ((y + s • v) 0) ((y + s • v) 1) ((y + s • v) 2) ((y + s • v) 3)) _ 0 at hsf
  change HasDerivAt (fun s => connectionWeakClockRate ((y + s • v) 0) ((y + s • v) 1) ((y + s • v) 2) ((y + s • v) 3)) _ 0 at hwf
  constructor
  · simpa [entranceStrongLogRate, entranceClockRate] using hsf.unique hsCurve
  · simpa [entranceWeakLogRate, entranceClockRate] using hwf.unique hwCurve

end BianchiIX
