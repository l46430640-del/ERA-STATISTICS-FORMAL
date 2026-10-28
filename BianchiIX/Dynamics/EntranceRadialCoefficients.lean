import BianchiIX.Dynamics.EntranceStablePhase
import BianchiIX.Dynamics.EntranceRegion

noncomputable section

namespace BianchiIX

def entranceWeakNumerator (y : ProjectiveState) : ℝ :=
  y 0 - 1 - y 1 * (y 3 - y 1) - (entranceStablePhase y - 1) * entranceStablePartial y 0

def entranceRadialStrongCoefficient (y : ProjectiveState) : ℝ :=
  ((entranceStablePhase y - 1) * ((1 - y 0) * entranceStablePartial y 0 +
    y 3 * (entranceStablePartial y 1 - entranceStablePartial y 3)) - y 2 ^ 2 -
    (1 / 2) * (entranceStablePhase y - 1) * y 2 * entranceStablePartial y 1) /
      (entranceStableRadius y * entranceClockRate y)

def entranceRadialWeakCoefficient (y : ProjectiveState) : ℝ :=
  entranceWeakNumerator y / (entranceStableRadius y * entranceClockRate y)

def entranceStrongRemainder (y : ProjectiveState) : ℝ :=
  (entranceStablePhase y - 1) * ((entranceStablePhase y - y 0) -
    (y 0 - 1) * (entranceStablePartial y 0 - 1)) +
  (entranceStablePhase y - 1) * y 3 * (entranceStablePartial y 1 - entranceStablePartial y 3) -
  (1 / 2) * (entranceStablePhase y - 1) * y 2 * entranceStablePartial y 1

theorem entranceWeakNumerator_eq (y : ProjectiveState) :
    entranceWeakNumerator y = y 0 - entranceStablePhase y - y 1 * (y 3 - y 1) -
      (entranceStablePhase y - 1) * (entranceStablePartial y 0 - 1) := by
  unfold entranceWeakNumerator
  ring

/-- The exact radial equation in the logarithmic active-wall clock, equation (C.18). -/
theorem entranceStableRadius_log_rate {y : ProjectiveState}
    (hm : 2 ≤ y 0) (hu : |y 1| < 1 / 200) (hw : |y 3| < 1 / 200) (hv : 0 < y 2) :
    fderiv ℝ entranceStableRadius y (projectiveField y) / entranceClockRate y =
      y 1 * y 2 * entranceRadialStrongCoefficient y + y 2 ^ 2 * entranceRadialWeakCoefficient y := by
  rw [entranceStableRadius_fderiv hm hu hw hv, entranceStablePhase_fderiv_field hm hu hw]
  change ((_ - 1) * _ + y 2 * activeVelocity (y 0) (y 1) (y 2) (y 3)) / _ / _ = _
  unfold entranceRadialStrongCoefficient entranceRadialWeakCoefficient entranceWeakNumerator
    entranceClockRate connectionSpeed activeVelocity coupling
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- The leading strong-wall term has an exact radial cancellation. -/
theorem entranceRadialStrongCoefficient_decomposition {y : ProjectiveState}
    (hr : entranceStableRadius y ≠ 0) (hD : entranceClockRate y ≠ 0) :
    entranceRadialStrongCoefficient y = -entranceStableRadius y / entranceClockRate y +
      entranceStrongRemainder y / (entranceStableRadius y * entranceClockRate y) := by
  unfold entranceRadialStrongCoefficient entranceStrongRemainder
  field_simp
  nlinarith only [entranceStableRadius_sq y]

theorem hasDerivAt_entranceStableRadius_scaled {Y : ℝ → ProjectiveState} {a t : ℝ}
    (hY : HasDerivAt Y (a • projectiveField (Y t)) t)
    (hm : 2 ≤ Y t 0) (hu : |Y t 1| < 1 / 200) (hw : |Y t 3| < 1 / 200)
    (hv : 0 < Y t 2) (hD : entranceClockRate (Y t) ≠ 0) :
    HasDerivAt (fun s => entranceStableRadius (Y s))
      (a * entranceClockRate (Y t) * (Y t 1 * Y t 2 * entranceRadialStrongCoefficient (Y t) +
        Y t 2 ^ 2 * entranceRadialWeakCoefficient (Y t))) t := by
  have H := ((contDiffAt_entranceStableRadius_two hm hu hw hv).differentiableAt
    (by norm_num)).hasFDerivAt.comp_hasDerivAt t hY
  rw [map_smul, smul_eq_mul] at H
  have hrate := (div_eq_iff hD).mp (entranceStableRadius_log_rate hm hu hw hv)
  convert! H using 1
  rw [hrate]
  ring

theorem normalized_entranceStableRadius_rate {x : NormalizedState} {t₀ t k : ℝ}
    (hc : stateConstraint x = 1) (hk : 7 / 4 ≤ k) (ht : t₀ ≤ t)
    (hA : 0 < normalizedProjectiveRate x t₀ t) :
    let Y := fun r => toProjectiveState (normalizedMaxCurve x t₀ r)
    entranceRegion k (Y t) → 0 < Y t 2 →
    HasDerivAt (fun r => entranceStableRadius (Y r))
      (normalizedProjectiveRate x t₀ t * entranceClockRate (Y t) *
        (Y t 1 * Y t 2 * entranceRadialStrongCoefficient (Y t) +
          Y t 2 ^ 2 * entranceRadialWeakCoefficient (Y t))) t ∧
      HasDerivAt (fun r => Real.log (Y r 2))
        (normalizedProjectiveRate x t₀ t * entranceClockRate (Y t)) t ∧
      0 < normalizedProjectiveRate x t₀ t * entranceClockRate (Y t) := by
  intro Y hy hv
  have H := normalizedMaxCurve_forward_of_constraint hc ht
  have hY := hasDerivAt_toProjectiveState_normalized H.1 hA.ne' H.2.1
  have hm : 2 ≤ Y t 0 := by linarith [(entranceRegion_phase hk hy).1]
  have hu : |Y t 1| < 1 / 200 := by rw [abs_of_nonneg hy.2.2.1.1]; linarith [hy.2.2.1.2]
  have hw : |Y t 3| < 1 / 200 := by rw [abs_of_nonneg hy.2.2.2.2.1]; linarith [hy.2.2.2.2.2]
  have hD := entranceRegion_clock_pos hk hy
  exact ⟨hasDerivAt_entranceStableRadius_scaled hY hm hu hw hv hD.ne',
    hasDerivAt_entranceLog_scaled hY hv.ne', mul_pos hA hD⟩

end BianchiIX
