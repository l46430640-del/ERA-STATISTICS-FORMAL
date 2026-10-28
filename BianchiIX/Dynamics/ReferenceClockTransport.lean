import BianchiIX.Dynamics.ReferenceShiftedVariation
import BianchiIX.Dynamics.ProjectiveClock
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

noncomputable section

namespace BianchiIX

open Set MeasureTheory

theorem referenceShiftClock_projective_rate (k s t : ℝ) :
    normalizedProjectiveRate (fromProjectiveState (referencePulse k s)) 0 (referenceShiftClock k s t) =
      6 / projectiveStateDenom (referencePulse k t) := by
  rw [normalizedProjectiveRate, (referenceShiftClock_normalized_orbit k s t).2]
  change 1 + (6 / projectiveStateDenom (referencePulse k t) - 1) = _
  ring

theorem referenceShiftClock_weighted_integral (k s t : ℝ) {f : ℝ → ℝ}
    (hf : ContinuousOn f (referenceShiftClock k s '' uIcc s t)) :
    (∫ u in 0..referenceShiftClock k s t,
      normalizedProjectiveRate (fromProjectiveState (referencePulse k s)) 0 u * f u) =
      ∫ r in s..t, f (referenceShiftClock k s r) := by
  let a := normalizedProjectiveRate (fromProjectiveState (referencePulse k s)) 0
  have ha : ContinuousOn a (referenceShiftClock k s '' uIcc s t) :=
    (continuousOn_normalizedProjectiveRate _ _).mono (by
      rintro u ⟨r, _, rfl⟩
      exact (referenceShiftClock_normalized_orbit k s r).1)
  have hp : Continuous (referencePulse k) :=
    continuous_iff_continuousAt.mpr (fun r => (hasDerivAt_referencePulse k r).continuousAt)
  have hd : Continuous (fun r => projectiveStateDenom (referencePulse k r) / 6) :=
    (continuous_projectiveStateDenom.comp hp).div_const 6
  have H := intervalIntegral.integral_comp_mul_deriv'
    (fun r (_ : r ∈ uIcc s t) => hasDerivAt_referenceShiftClock k s r) hd.continuousOn (ha.mul hf)
  rw [referenceShiftClock_initial] at H
  calc
    _ = ∫ r in s..t, (a (referenceShiftClock k s r) * f (referenceShiftClock k s r)) *
        (projectiveStateDenom (referencePulse k r) / 6) := H.symm
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro r _
      change (normalizedProjectiveRate _ 0 _ * _) * _ = _
      rw [referenceShiftClock_projective_rate]
      have hD := (referencePulse_denom_pos k r).ne'
      field_simp

/-- Accumulated projective time is exactly the parameter difference along the reference orbit. -/
theorem referenceShiftClock_elapsed (k s t : ℝ) :
    (∫ u in 0..referenceShiftClock k s t,
      normalizedProjectiveRate (fromProjectiveState (referencePulse k s)) 0 u) = t - s := by
  simpa only [mul_one, intervalIntegral.integral_const, smul_eq_mul, mul_one] using
    referenceShiftClock_weighted_integral k s t (f := fun _ => (1 : ℝ)) continuousOn_const

end BianchiIX
