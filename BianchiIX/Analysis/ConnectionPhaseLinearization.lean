import BianchiIX.Analysis.ConnectionPhaseNumerator

noncomputable section

namespace BianchiIX

open Filter
open scoped Topology

def connectionPhaseGPartials (m u v w : ℝ) (i : Fin 4) : ℝ :=
  u * connectionPhaseAPartials m u v w i + (v * w) ^ 2 * connectionPhaseBPartials m u v w i +
    (![0, u * connectionPhaseA m u v w, 2 * (v * w) ^ 2 * connectionPhaseB m u v w,
      2 * (v * w) ^ 2 * connectionPhaseB m u v w] : Fin 4 → ℝ) i

theorem connectionPhaseGPartials_phase {m u v w : ℝ} (hD : connectionSpeed m u v w ≠ 0) :
    connectionPhaseGPartials m u v w 0 = connectionPhaseGJ m u v w := by
  simp only [connectionPhaseGPartials, Matrix.cons_val_zero, add_zero, connectionPhaseAPartials_phase hD]
  rfl

theorem hasDerivAt_connectionPhaseG_weighted {m u v w : ℝ → ℝ} {t : ℝ} (d : Fin 4 → ℝ)
    (hm : HasDerivAt m (d 0 / matchingPhaseSlope (m t) (v t) (w t) +
      matchingPhaseVVariation (m t) (v t) (w t) * d 2 + matchingPhaseWVariation (m t) (v t) (w t) * d 3) t)
    (hu : HasDerivAt u (u t * d 1) t) (hv : HasDerivAt v (v t * d 2) t) (hw : HasDerivAt w (w t * d 3) t)
    (hmt : 1 < m t) (hf : matchingPhaseSlope (m t) (v t) (w t) ≠ 0)
    (hD : connectionSpeed (m t) (u t) (v t) (w t) ≠ 0) :
    HasDerivAt (fun s => connectionPhaseG (m s) (u s) (v s) (w s))
      (∑ i : Fin 4, connectionPhaseGPartials (m t) (u t) (v t) (w t) i * d i) t := by
  have hA := hasDerivAt_connectionPhaseA_weighted d hm hu hv hw hmt hf hD
  have hB := hasDerivAt_connectionPhaseB_weighted d hm hu hv hw hmt hD
  have H := (hu.mul hA).add (((hv.mul hw).pow 2).mul hB)
  have heq : (fun s => connectionPhaseG (m s) (u s) (v s) (w s)) =
      (fun s => u s * connectionPhaseA (m s) (u s) (v s) (w s) +
        (v s * w s) ^ 2 * connectionPhaseB (m s) (u s) (v s) (w s)) := by
    funext s
    exact connectionPhaseG_decomposition _ _ _ _
  rw [heq]
  apply H.congr_deriv
  simp [Fin.sum_univ_succ, connectionPhaseGPartials, Pi.mul_apply]
  ring

theorem hasDerivAt_connectionPhaseG_weighted_in_phase {M : MatchingPhaseParameters → ℝ}
    {p : MatchingPhaseParameters} {u : ℝ} (hM : DifferentiableAt ℝ M p) (hm : 1 < M p)
    (hf : matchingPhaseSlope (M p) (p 1) (p 2) ≠ 0)
    (heq : ∀ᶠ q in 𝓝 p, matchingPhase (M q) (q 1) (q 2) = q 0)
    (hD : connectionSpeed (M p) u (p 1) (p 2) ≠ 0) (d : Fin 4 → ℝ) :
    HasDerivAt (fun t => connectionPhaseG
      (M (matchingPhaseWeightedBase p ![d 0, d 2, d 3] t))
      (u * Real.exp (t * d 1)) (p 1 * Real.exp (t * d 2)) (p 2 * Real.exp (t * d 3)))
      (∑ i : Fin 4, connectionPhaseGPartials (M p) u (p 1) (p 2) i * d i) 0 := by
  have hexp (c k : ℝ) : HasDerivAt (fun t => c * Real.exp (t * k)) (c * k) 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).mul_const k).exp).const_mul c
  have hm' := hasDerivAt_matchingPhase_inverse_weighted hM hm hf heq ![d 0, d 2, d 3]
  have H := hasDerivAt_connectionPhaseG_weighted
    (m := fun t => M (matchingPhaseWeightedBase p ![d 0, d 2, d 3] t))
    (u := fun t => u * Real.exp (t * d 1))
    (v := fun t => p 1 * Real.exp (t * d 2))
    (w := fun t => p 2 * Real.exp (t * d 3)) (t := 0) d
    (by simpa [matchingPhaseWeightedBase_zero] using hm')
    (by simpa only [zero_mul, Real.exp_zero, mul_one] using hexp u (d 1))
    (by simpa only [zero_mul, Real.exp_zero, mul_one] using hexp (p 1) (d 2))
    (by simpa only [zero_mul, Real.exp_zero, mul_one] using hexp (p 2) (d 3))
    (by simpa only [matchingPhaseWeightedBase_zero] using hm)
    (by simpa only [matchingPhaseWeightedBase_zero, zero_mul, Real.exp_zero, mul_one] using hf)
    (by simpa only [matchingPhaseWeightedBase_zero, zero_mul, Real.exp_zero, mul_one] using hD)
  simpa only [matchingPhaseWeightedBase_zero, zero_mul, Real.exp_zero, mul_one] using H

end BianchiIX
