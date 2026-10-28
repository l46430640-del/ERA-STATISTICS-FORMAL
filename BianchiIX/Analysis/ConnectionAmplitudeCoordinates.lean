import BianchiIX.Analysis.ConnectionAmplitudeDifferential

noncomputable section

namespace BianchiIX

open Filter
open scoped Topology

/-- These are derivatives of the actual inverse-coordinate curves, including at a zero wall. -/
theorem hasDerivAt_connection_clock_in_phase {M : MatchingPhaseParameters → ℝ}
    {p : MatchingPhaseParameters} {u : ℝ} (hM : DifferentiableAt ℝ M p) (hm : 1 < M p)
    (hf : matchingPhaseSlope (M p) (p 1) (p 2) ≠ 0)
    (heq : ∀ᶠ q in 𝓝 p, matchingPhase (M q) (q 1) (q 2) = q 0)
    (hD : connectionSpeed (M p) u (p 1) (p 2) ≠ 0) (d : Fin 4 → ℝ) :
    HasDerivAt (fun t => connectionStrongClockRate
      (M (matchingPhaseWeightedBase p ![d 0, d 2, d 3] t))
      (u * Real.exp (t * d 1)) (p 1 * Real.exp (t * d 2)) (p 2 * Real.exp (t * d 3)))
      (∑ i : Fin 4, connectionStrongClockPartials (M p) u (p 1) (p 2) i * d i) 0 ∧
    HasDerivAt (fun t => connectionWeakClockRate
      (M (matchingPhaseWeightedBase p ![d 0, d 2, d 3] t))
      (u * Real.exp (t * d 1)) (p 1 * Real.exp (t * d 2)) (p 2 * Real.exp (t * d 3)))
      (∑ i : Fin 4, connectionWeakClockPartials (M p) u (p 1) (p 2) i * d i) 0 := by
  have hexp (c k : ℝ) : HasDerivAt (fun t => c * Real.exp (t * k)) (c * k) 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).mul_const k).exp).const_mul c
  have hm' := hasDerivAt_matchingPhase_inverse_weighted hM hm hf heq ![d 0, d 2, d 3]
  have H := hasDerivAt_connection_clock_weighted_curves
    (m := fun t => M (matchingPhaseWeightedBase p ![d 0, d 2, d 3] t))
    (u := fun t => u * Real.exp (t * d 1))
    (v := fun t => p 1 * Real.exp (t * d 2))
    (w := fun t => p 2 * Real.exp (t * d 3)) (t := 0) d
    (by simpa [matchingPhaseWeightedBase_zero] using hm')
    (by simpa only [zero_mul, Real.exp_zero, mul_one] using hexp u (d 1))
    (by simpa only [zero_mul, Real.exp_zero, mul_one] using hexp (p 1) (d 2))
    (by simpa only [zero_mul, Real.exp_zero, mul_one] using hexp (p 2) (d 3))
    (by simpa only [matchingPhaseWeightedBase_zero, zero_mul, Real.exp_zero, mul_one] using hD)
  simpa only [matchingPhaseWeightedBase_zero, zero_mul, Real.exp_zero, mul_one] using H

end BianchiIX
