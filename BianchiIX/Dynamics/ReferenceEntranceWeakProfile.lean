import BianchiIX.Dynamics.ReferenceEntranceResponse
import BianchiIX.Dynamics.EntranceWeakFactorization
import Mathlib.Analysis.Calculus.Deriv.MeanValue

noncomputable section

namespace BianchiIX

open Set

def referenceEntrancePhase (k v t : ℝ) : ℝ :=
  referencePulse k (-referenceHeightTime k v + t) 0 - 1

def referenceEntranceWeakResponse (k v : ℝ) : ℝ :=
  -(v ^ 2 / k) * ((∫ t in 0..referenceEntranceDuration k v,
    Real.exp (-4 * t) / (referenceEntrancePhase k v t + 2) ^ 2) +
    Real.sqrt (k ^ 2 - 1) / (2 * (Real.sqrt (k ^ 2 - 1) + 2)) *
      Real.exp (-4 * referenceEntranceDuration k v))

theorem antitone_referencePulse_phase (k : ℝ) : Antitone (fun t => referencePulse k t 0) := by
  apply antitone_of_hasDerivAt_nonpos (fun t => (hasDerivAt_pi.mp (hasDerivAt_referencePulse k t)) 0)
  intro t
  dsimp [projectiveField, phaseVelocity, coupling, referencePulse]
  nlinarith only [sq_nonneg (k / Real.cosh (k * t))]

theorem referenceEntranceDuration_pos {k v : ℝ} (hk : 1 < k) (hv : 0 < v ∧ v < 1) :
    0 < referenceEntranceDuration k v :=
  sub_pos.mpr (referenceHalfTime_lt_heightTime hk hv)

theorem continuous_referenceEntrancePhase (k v : ℝ) : Continuous (referenceEntrancePhase k v) := by
  have hp : Continuous (referencePulse k) :=
    continuous_iff_continuousAt.mpr (fun t => (hasDerivAt_referencePulse k t).continuousAt)
  exact (((continuous_apply 0).comp hp).comp (continuous_const.add continuous_id)).sub continuous_const

theorem referenceEntrancePhase_eq {k v : ℝ} (hk : 0 < k) (t : ℝ) :
    referenceEntrancePhase k v t = k * Real.tanh (Real.arcosh (k / v) - k * t) := by
  have ha : k * (-referenceHeightTime k v + t) = -(Real.arcosh (k / v) - k * t) := by
    dsimp [referenceHeightTime]
    field_simp
    ring
  dsimp only [referenceEntrancePhase, referencePulse, Matrix.cons_val_zero]
  rw [ha, Real.tanh_neg]
  ring

theorem referenceEntrancePhase_terminal {k v : ℝ} (hk : 1 < k) :
    referenceEntrancePhase k v (referenceEntranceDuration k v) = Real.sqrt (k ^ 2 - 1) := by
  have ht : -referenceHeightTime k v + referenceEntranceDuration k v = -referenceHalfTime k := by
    dsimp [referenceEntranceDuration]
    ring
  rw [referenceEntrancePhase, ht, referencePulse_entry hk]
  dsimp
  ring

theorem referenceEntrancePhase_lower {k v t : ℝ} (hk : 7 / 4 ≤ k)
    (ht : t ≤ referenceEntranceDuration k v) :
    1 ≤ Real.sqrt (k ^ 2 - 1) ∧ Real.sqrt (k ^ 2 - 1) ≤ referenceEntrancePhase k v t := by
  have hk1 : 1 < k := by linarith
  constructor
  · have H := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ k ^ 2 - 1 by nlinarith)
    simpa only [Real.sqrt_one] using H
  · rw [← referenceEntrancePhase_terminal (v := v) hk1]
    change referencePulse k (-referenceHeightTime k v + referenceEntranceDuration k v) 0 - 1 ≤
      referencePulse k (-referenceHeightTime k v + t) 0 - 1
    have H := antitone_referencePulse_phase k
      (show -referenceHeightTime k v + t ≤ -referenceHeightTime k v + referenceEntranceDuration k v from
        by linarith only [ht])
    linarith only [H]

theorem referenceEntrance_weak_weights {k v t : ℝ} (hk : 7 / 4 ≤ k)
    (ht : t ≤ referenceEntranceDuration k v) :
    entranceWeakDriftWeight (referencePulse k (-referenceHeightTime k v + t)) =
        1 / (k * (referenceEntrancePhase k v t + 2) ^ 2) ∧
      entranceWeakCorrectionWeight (referencePulse k (-referenceHalfTime k)) =
        Real.sqrt (k ^ 2 - 1) / (2 * k * (Real.sqrt (k ^ 2 - 1) + 2)) := by
  have hk0 : 0 < k := by linarith
  have hm : 2 ≤ referencePulse k (-referenceHeightTime k v + t) 0 := by
    have H := referenceEntrancePhase_lower hk ht
    change _ ∧ _ ≤ referencePulse k (-referenceHeightTime k v + t) 0 - 1 at H
    linarith [H.1, H.2]
  have H := entranceWeak_weights_zero_walls hm rfl rfl
    (referencePulse_active_pos hk0 (-referenceHeightTime k v + t))
  rw [referencePulse_radius hk0.le] at H
  have hs := (referenceEntrancePhase_lower (v := v) hk (le_refl (referenceEntranceDuration k v))).1
  have hm' : 2 ≤ referencePulse k (-referenceHalfTime k) 0 := by
    rw [referencePulse_entry (show 1 < k by linarith)]
    change 2 ≤ 1 + Real.sqrt (k ^ 2 - 1)
    linarith
  have HE := (entranceWeak_weights_zero_walls hm' rfl rfl
    (referencePulse_active_pos hk0 (-referenceHalfTime k))).2
  rw [referencePulse_radius hk0.le, referencePulse_entry (show 1 < k by linarith)] at HE
  constructor
  · convert! H.1 using 2
    dsimp [referenceEntrancePhase]
    ring
  · rw [referencePulse_entry (show 1 < k by linarith)]
    convert! HE using 1
    dsimp
    ring

end BianchiIX
