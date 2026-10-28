import BianchiIX.Dynamics.EntranceWeakCoefficient
import BianchiIX.Dynamics.EntranceRadialDriftBounds
import BianchiIX.Dynamics.EntranceRadiusCorrection

noncomputable section

namespace BianchiIX

def entranceWeakDriftWeight (y : ProjectiveState) : ℝ :=
  2 / (entranceStableRadius y * stableWeakRadius (y 0) (y 3) *
    (stableWeakRadius (y 0) (y 3) + y 0 + 1))

def entranceWeakCorrectionWeight (y : ProjectiveState) : ℝ :=
  (stableWeakRadius (y 0) (y 3) + y 0 - 3) /
    ((entranceStableRadius y + coreRadius (y 0) (y 2)) *
      (stableWeakRadius (y 0) (y 3) + y 0 + 1))

theorem entranceWeak_weights_pos {y : ProjectiveState} (hm : 2 ≤ y 0) (hv : 0 < y 2) :
    0 < entranceWeakDriftWeight y ∧ 0 < entranceWeakCorrectionWeight y := by
  have hS := stableWeakRadius_pos (w := y 3) (show -1 < y 0 by linarith)
  have hSlo : y 0 + 1 ≤ stableWeakRadius (y 0) (y 3) := phaseNorm_ge (by linarith)
  have hr := entranceStableRadius_pos hv
  have hR := coreRadius_pos (m := y 0) hv
  have hn : 0 < stableWeakRadius (y 0) (y 3) + y 0 - 3 := by linarith
  have hd : 0 < stableWeakRadius (y 0) (y 3) + y 0 + 1 := by linarith
  exact ⟨div_pos (by norm_num) (mul_pos (mul_pos hr hS) hd),
    div_pos hn (mul_pos (add_pos hr hR) hd)⟩

/-- Rationalization factors the exact terminal correction by the weak wall squared. -/
theorem entranceRadiusCorrection_zero_strong {y : ProjectiveState}
    (hm : 2 ≤ y 0) (hu : y 1 = 0) (hw : |y 3| ≤ 1 / 200) (hv : 0 < y 2) :
    entranceRadiusCorrection y = (y 3) ^ 2 * entranceWeakCorrectionWeight y := by
  let S := stableWeakRadius (y 0) (y 3)
  let r := entranceStableRadius y
  let R := coreRadius (y 0) (y 2)
  have hr := entranceStableRadius_sq y
  rw [entranceStablePhase_weak hm hu hw] at hr
  have hR := coreRadius_sq (y 0) (y 2)
  have hS := stableWeakRadius_sq (y 0) (y 3)
  have hd : (r - R) * (r + R) = (y 3) ^ 2 - 4 * (S - y 0 - 1) := by
    dsimp only [coreEnergy] at hR
    change r ^ 2 = (S - 1 - 1) ^ 2 + (y 2) ^ 2 at hr
    change S ^ 2 = (y 0 + 1) ^ 2 + (y 3) ^ 2 at hS
    nlinarith only [hr, hR, hS]
  have hrat : (S - y 0 - 1) * (S + y 0 + 1) = (y 3) ^ 2 := by
    nlinarith only [hS]
  have hr0 : 0 < r := entranceStableRadius_pos hv
  have hR0 : 0 < R := coreRadius_pos hv
  have hS0 : 0 < S := stableWeakRadius_pos (by linarith)
  have hden : (r + R) * (S + y 0 + 1) ≠ 0 :=
    (mul_pos (add_pos hr0 hR0) (by linarith)).ne'
  change r - R = (y 3) ^ 2 * ((S + y 0 - 3) / ((r + R) * (S + y 0 + 1)))
  rw [← mul_div_assoc]
  apply (eq_div_iff hden).mpr
  calc
    _ = ((r - R) * (r + R)) * (S + y 0 + 1) := by ring
    _ = ((y 3) ^ 2 - 4 * (S - y 0 - 1)) * (S + y 0 + 1) := by rw [hd]
    _ = _ := by nlinarith only [hrat]

theorem entranceRadialDrift_zero_strong {y : ProjectiveState}
    (hm : 2 ≤ y 0) (hu : y 1 = 0) (hw : |y 3| < 1 / 200) :
    entranceRadialDrift y = -(y 2 * y 3) ^ 2 * entranceWeakDriftWeight y / (y 0 - 1) := by
  have hclock : entranceClockRate y = y 0 - 1 := by
    simp [entranceClockRate, connectionSpeed, hu, coupling]
  rw [entranceRadialDrift, hu, zero_mul, zero_mul, zero_add,
    entranceRadialWeakCoefficient, entranceWeakNumerator_weak hm hu hw, hclock]
  dsimp [entranceWeakDriftWeight]
  simp only [div_eq_mul_inv, mul_inv_rev, add_assoc]
  ring

theorem hasDerivAt_entranceStableRadius_zero_strong {Y : ℝ → ProjectiveState} {a t : ℝ}
    (hY : HasDerivAt Y (a • projectiveField (Y t)) t)
    (hm : 2 ≤ Y t 0) (hu : Y t 1 = 0) (hw : |Y t 3| < 1 / 200) (hv : 0 < Y t 2) :
    HasDerivAt (fun s => entranceStableRadius (Y s))
      (-a * (Y t 2 * Y t 3) ^ 2 * entranceWeakDriftWeight (Y t)) t := by
  have hclock : entranceClockRate (Y t) = Y t 0 - 1 := by
    simp [entranceClockRate, connectionSpeed, hu, coupling]
  have hd : Y t 0 - 1 ≠ 0 := by linarith
  have H := hasDerivAt_entranceStableRadius_scaled hY hm (by rw [hu]; norm_num) hw hv
    (by rw [hclock]; exact hd)
  change HasDerivAt _ (a * entranceClockRate (Y t) * entranceRadialDrift (Y t)) t at H
  rw [entranceRadialDrift_zero_strong hm hu hw, hclock] at H
  convert! H using 1
  field_simp

theorem continuousAt_entranceWeak_weights {y : ProjectiveState}
    (hm : 2 ≤ y 0) (hu : |y 1| < 1 / 200) (hw : |y 3| < 1 / 200) (hv : 0 < y 2) :
    ContinuousAt entranceWeakDriftWeight y ∧ ContinuousAt entranceWeakCorrectionWeight y := by
  have hr := (contDiffAt_entranceStableRadius_two hm hu hw hv).continuousAt
  have hR : ContinuousAt (fun z : ProjectiveState => coreRadius (z 0) (z 2)) y := by
    unfold coreRadius coreEnergy
    fun_prop
  have hS : ContinuousAt (fun z : ProjectiveState => stableWeakRadius (z 0) (z 3)) y := by
    unfold stableWeakRadius phaseNorm
    fun_prop
  have hs := stableWeakRadius_pos (w := y 3) (show -1 < y 0 by linarith)
  have hs' : stableWeakRadius (y 0) (y 3) + y 0 + 1 ≠ 0 := by linarith
  have hr' := (entranceStableRadius_pos hv).ne'
  have hsum := (add_pos (entranceStableRadius_pos hv) (coreRadius_pos (m := y 0) hv)).ne'
  exact ⟨continuousAt_const.div ((hr.mul hS).mul ((hS.add (continuous_apply 0).continuousAt).add_const 1))
      (mul_ne_zero (mul_ne_zero hr' hs.ne') hs'),
    (((hS.add (continuous_apply 0).continuousAt).sub_const 3).div
      ((hr.add hR).mul ((hS.add (continuous_apply 0).continuousAt).add_const 1)) (mul_ne_zero hsum hs'))⟩

theorem entranceWeak_weights_zero_walls {y : ProjectiveState}
    (hm : 2 ≤ y 0) (hu : y 1 = 0) (hw : y 3 = 0) (hv : 0 < y 2) :
    entranceWeakDriftWeight y = 1 / (coreRadius (y 0) (y 2) * (y 0 + 1) ^ 2) ∧
      entranceWeakCorrectionWeight y = (y 0 - 1) / (2 * coreRadius (y 0) (y 2) * (y 0 + 1)) := by
  have hS : stableWeakRadius (y 0) (y 3) = y 0 + 1 := by
    simp only [hw, stableWeakRadius, phaseNorm, zero_pow (by decide : (2 : ℕ) ≠ 0), add_zero]
    exact Real.sqrt_sq (by linarith)
  have hp : entranceStablePhase y = y 0 := by
    rw [entranceStablePhase_weak hm hu (by rw [hw]; norm_num), hS]
    ring
  have hr : entranceStableRadius y = coreRadius (y 0) (y 2) := by
    dsimp [entranceStableRadius, coreRadius, coreEnergy, phaseNorm]
    rw [hp]
  have hR := (coreRadius_pos (m := y 0) hv).ne'
  have hm' : y 0 + 1 ≠ 0 := by linarith
  constructor
  · dsimp [entranceWeakDriftWeight]
    rw [hS, hr]
    field_simp
    ring
  · dsimp [entranceWeakCorrectionWeight]
    rw [hS, hr]
    field_simp
    ring

end BianchiIX
