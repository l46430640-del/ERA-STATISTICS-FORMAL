import BianchiIX.Dynamics.RestartProjectionPhase

noncomputable section

namespace BianchiIX

abbrev RestartProjectionNormal := Fin 3 → ℝ
abbrev RestartProjectionCenter := Fin 2 → ℝ
abbrev RestartProjectionParameters := RestartProjectionNormal × RestartProjectionCenter

def restartProjectionScaledState (p : RestartProjectionParameters) : RestartRadialState :=
  (p.1 0 * p.1 1, ![p.1 0 * p.2 0, p.1 0 * p.2 1, p.1 0 * p.1 2])

def restartProjectionScaledDefect (p : RestartProjectionParameters) : ℝ :=
  (p.2 0) ^ 2 + curvature (p.1 1) (p.2 1) (p.1 2)

def restartProjectionScaledHeight (p : RestartProjectionParameters) : ℝ :=
  restartProjectionScaledDefect p /
    (1 + Real.sqrt (1 - (p.1 0) ^ 2 * restartProjectionScaledDefect p))

def restartProjectionScaledDenom (p : RestartProjectionParameters) : ℝ :=
  (Real.sqrt 3 * p.2 0 - p.1 0 * restartProjectionScaledHeight p) ^ 2 + 3 * (p.2 1) ^ 2

def restartProjectionScaledError (p : RestartProjectionParameters) : ℝ :=
  2 * restartProjectionScaledHeight p / Real.sqrt (restartProjectionScaledDenom p) -
    Real.sqrt ((p.2 0) ^ 2 + (p.2 1 - p.1 2) ^ 2) / Real.sqrt 3

theorem restartProjectionDefect_scaled (p : RestartProjectionParameters) :
    restartProjectionDefect (restartProjectionScaledState p) =
      (p.1 0) ^ 2 * restartProjectionScaledDefect p := by
  unfold restartProjectionDefect restartProjectionScaledState restartProjectionScaledDefect curvature
  dsimp
  ring

theorem restartProjectionHeight_scaled (p : RestartProjectionParameters) :
    restartProjectionHeight (restartProjectionScaledState p) =
      (p.1 0) ^ 2 * restartProjectionScaledHeight p := by
  rw [restartProjectionHeight, restartProjectionDefect_scaled]
  unfold restartProjectionScaledHeight
  ring

/-- Homogeneous scaling removes the small denominator from the phase difference. -/
theorem restartProjectionPhase_scaled {p : RestartProjectionParameters} (hr : 0 < p.1 0) :
    restartProjectionPhase (restartProjectionScaledState p) -
      restartRadialPhase (restartProjectionScaledState p).2 =
        p.1 0 * restartProjectionScaledError p := by
  have hden : (Real.sqrt 3 * (restartProjectionScaledState p).2 0 -
      restartProjectionHeight (restartProjectionScaledState p)) ^ 2 +
      3 * ((restartProjectionScaledState p).2 1) ^ 2 =
        (p.1 0) ^ 2 * restartProjectionScaledDenom p := by
    rw [restartProjectionHeight_scaled]
    dsimp only [restartProjectionScaledState, restartProjectionScaledDenom]
    change (Real.sqrt 3 * (p.1 0 * p.2 0) - (p.1 0) ^ 2 * restartProjectionScaledHeight p) ^ 2 +
      3 * (p.1 0 * p.2 1) ^ 2 = _
    ring
  have hrad : restartRadialNorm (restartProjectionScaledState p).2 =
      p.1 0 * Real.sqrt ((p.2 0) ^ 2 + (p.2 1 - p.1 2) ^ 2) := by
    unfold restartRadialNorm
    change Real.sqrt ((p.1 0 * p.2 0) ^ 2 + (p.1 0 * p.2 1 - p.1 0 * p.1 2) ^ 2) = _
    rw [show (p.1 0 * p.2 0) ^ 2 + (p.1 0 * p.2 1 - p.1 0 * p.1 2) ^ 2 =
      (p.1 0) ^ 2 * ((p.2 0) ^ 2 + (p.2 1 - p.1 2) ^ 2) by ring,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hr.le]
  rw [restartProjectionPhase, hden, restartProjectionHeight_scaled,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hr.le, restartRadialPhase, hrad]
  unfold restartProjectionScaledError
  rw [show 2 * (p.1 0 ^ 2 * restartProjectionScaledHeight p) =
    p.1 0 * (p.1 0 * (2 * restartProjectionScaledHeight p)) by ring,
    mul_div_mul_left _ _ hr.ne']
  ring

theorem restartProjectionScaledError_axis (X : RestartProjectionCenter) :
    restartProjectionScaledError (0, X) = 0 := by
  have hsqrt : (Real.sqrt (3 : ℝ)) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hden : restartProjectionScaledDenom (0, X) = 3 * ((X 0) ^ 2 + (X 1) ^ 2) := by
    simp only [restartProjectionScaledDenom, Pi.zero_apply, zero_mul, sub_zero, mul_pow, hsqrt]
    ring
  have hheight : restartProjectionScaledHeight (0, X) = ((X 0) ^ 2 + (X 1) ^ 2) / 2 := by
    norm_num [restartProjectionScaledHeight, restartProjectionScaledDefect, curvature]
  rw [restartProjectionScaledError, hden, hheight, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3)]
  simp only [Pi.zero_apply, sub_zero]
  let R := Real.sqrt ((X 0) ^ 2 + (X 1) ^ 2)
  have hR : R ^ 2 = (X 0) ^ 2 + (X 1) ^ 2 := Real.sq_sqrt (by positivity)
  change 2 * (((X 0) ^ 2 + (X 1) ^ 2) / 2) / (Real.sqrt 3 * R) - R / Real.sqrt 3 = 0
  rw [← hR]
  by_cases hR0 : R = 0
  · simp [hR0]
  · have h3 : Real.sqrt (3 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
    field_simp
    ring

theorem contDiffAt_restartProjectionScaledError {p : RestartProjectionParameters}
    (hr : 0 < 1 - (p.1 0) ^ 2 * restartProjectionScaledDefect p)
    (hd : 0 < restartProjectionScaledDenom p)
    (hv : 0 < (p.2 0) ^ 2 + (p.2 1 - p.1 2) ^ 2) (k : WithTop ℕ∞) :
    ContDiffAt ℝ k restartProjectionScaledError p := by
  have HD : ContDiffAt ℝ k restartProjectionScaledDefect p := by
    unfold restartProjectionScaledDefect curvature
    fun_prop
  have HR : ContDiffAt ℝ k (fun q : RestartProjectionParameters =>
      1 - (q.1 0) ^ 2 * restartProjectionScaledDefect q) p := by fun_prop
  have HA : ContDiffAt ℝ k restartProjectionScaledHeight p := by
    apply HD.div ((contDiffAt_const).add (HR.sqrt hr.ne'))
    exact ne_of_gt (by positivity : 0 < 1 + Real.sqrt (1 - (p.1 0) ^ 2 * restartProjectionScaledDefect p))
  have Hden : ContDiffAt ℝ k restartProjectionScaledDenom p := by
    unfold restartProjectionScaledDenom
    fun_prop
  apply ((contDiffAt_const.mul HA).div (Hden.sqrt hd.ne') (ne_of_gt (Real.sqrt_pos.mpr hd))).sub
  have HV : ContDiffAt ℝ k (fun q : RestartProjectionParameters =>
      (q.2 0) ^ 2 + (q.2 1 - q.1 2) ^ 2) p := by fun_prop
  exact (HV.sqrt hv.ne').div_const _

theorem contDiffAt_restartProjectionScaledError_axis {X : RestartProjectionCenter}
    (hv : X 1 ≠ 0) (k : WithTop ℕ∞) :
    ContDiffAt ℝ k restartProjectionScaledError (0, X) := by
  apply contDiffAt_restartProjectionScaledError
  · simp
  · simp only [restartProjectionScaledDenom, Pi.zero_apply, zero_mul, sub_zero]
    have H := sq_pos_of_ne_zero hv
    nlinarith only [H, sq_nonneg (Real.sqrt 3 * X 0)]
  · simp only [Pi.zero_apply, sub_zero]
    exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero hv)

end BianchiIX
