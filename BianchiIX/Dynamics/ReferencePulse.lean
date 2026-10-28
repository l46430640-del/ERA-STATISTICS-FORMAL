import BianchiIX.Dynamics.ProjectiveState
import Mathlib.Analysis.SpecialFunctions.Arcosh

noncomputable section

namespace BianchiIX

def referencePulse (k t : ℝ) : ProjectiveState :=
  ![1 - k * Real.tanh (k * t), 0, k / Real.cosh (k * t), 0]

theorem hasDerivAt_real_tanh (z : ℝ) :
    HasDerivAt Real.tanh (1 / Real.cosh z ^ 2) z := by
  convert! (Real.hasDerivAt_sinh z).div (Real.hasDerivAt_cosh z)
    (ne_of_gt (Real.cosh_pos z)) using 1
  · ext x
    exact Real.tanh_eq_sinh_div_cosh x
  · rw [← pow_two, ← pow_two, Real.cosh_sq_sub_sinh_sq]

theorem referencePulse_energy (k t : ℝ) :
    coreEnergy (referencePulse k t 0) (referencePulse k t 2) = k ^ 2 := by
  dsimp [referencePulse, coreEnergy]
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp
  linear_combination -k ^ 2 * Real.cosh_sq_sub_sinh_sq (k * t)

theorem hasDerivAt_referencePulse (k t : ℝ) :
    HasDerivAt (referencePulse k) (projectiveField (referencePulse k t)) t := by
  have hz : HasDerivAt (fun s : ℝ => k * s) k t := by
    simpa using (hasDerivAt_id t).const_mul k
  have hm := (((hasDerivAt_real_tanh (k * t)).comp t hz).const_mul k).const_sub 1
  have hv := (hasDerivAt_const t k).div hz.cosh (ne_of_gt (Real.cosh_pos (k * t)))
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · convert! hm using 1
    dsimp [projectiveField, referencePulse, phaseVelocity, coupling]
    ring
  · convert! hasDerivAt_const t (0 : ℝ) using 1
    simp [projectiveField, referencePulse, strongVelocity]
  · convert! hv using 1
    dsimp [projectiveField, referencePulse, activeVelocity, coupling]
    rw [Real.tanh_eq_sinh_div_cosh]
    ring
  · convert! hasDerivAt_const t (0 : ℝ) using 1
    simp [projectiveField, referencePulse, weakVelocity]

theorem referencePulse_denom (k t : ℝ) :
    projectiveStateDenom (referencePulse k t) = k ^ 2 + 4 - 2 * k * Real.tanh (k * t) := by
  have he := referencePulse_energy k t
  dsimp [projectiveStateDenom, projectiveDenom, referencePulse, curvature, coreEnergy] at *
  nlinarith only [he]

theorem referencePulse_denom_pos (k t : ℝ) :
    0 < projectiveStateDenom (referencePulse k t) := by
  dsimp [projectiveStateDenom, projectiveDenom, referencePulse, curvature]
  nlinarith only [sq_nonneg (1 - k * Real.tanh (k * t)), sq_nonneg (k / Real.cosh (k * t))]

theorem referencePulse_active_pos {k : ℝ} (hk : 0 < k) (t : ℝ) :
    0 < referencePulse k t 2 := div_pos hk (Real.cosh_pos _)

end BianchiIX
