import BianchiIX.Analysis.MatchingKernelVariation
import BianchiIX.Analysis.ConnectionAmplitudeDifferential

noncomputable section

namespace BianchiIX

open Filter
open scoped Topology

def connectionPhaseA (m u v w : ℝ) : ℝ :=
  -(matchingPhaseSlope m v w * (v - w) + (v + w - u) * matchingPhaseWeight m v w) /
    connectionSpeed m u v w

def connectionPhaseB (m u v w : ℝ) : ℝ := matchingPhaseKernel m v w / connectionSpeed m u v w

def connectionPhaseG (m u v w : ℝ) : ℝ := matchingPhaseRate m u v w / connectionSpeed m u v w

theorem connectionPhaseG_decomposition (m u v w : ℝ) :
    connectionPhaseG m u v w = u * connectionPhaseA m u v w + (v * w) ^ 2 * connectionPhaseB m u v w := by
  dsimp [connectionPhaseG, connectionPhaseA, connectionPhaseB, matchingPhaseRate, coupling]
  ring

def connectionSpeedPartials (m u v w : ℝ) : Fin 4 → ℝ :=
  ![1 / matchingPhaseSlope m v w, -u * (v + w - 2 * u),
    matchingPhaseVVariation m v w - u * v, matchingPhaseWVariation m v w - u * w]

def connectionPhaseBPartials (m u v w : ℝ) (i : Fin 4) : ℝ :=
  matchingPhaseKernelPartials m v w i / connectionSpeed m u v w -
    matchingPhaseKernel m v w * connectionSpeedPartials m u v w i / connectionSpeed m u v w ^ 2

theorem hasDerivAt_connectionSpeed_weighted {m u v w : ℝ → ℝ} {t : ℝ} (d : Fin 4 → ℝ)
    (hm : HasDerivAt m (d 0 / matchingPhaseSlope (m t) (v t) (w t) +
      matchingPhaseVVariation (m t) (v t) (w t) * d 2 + matchingPhaseWVariation (m t) (v t) (w t) * d 3) t)
    (hu : HasDerivAt u (u t * d 1) t) (hv : HasDerivAt v (v t * d 2) t) (hw : HasDerivAt w (w t * d 3) t) :
    HasDerivAt (fun s => connectionSpeed (m s) (u s) (v s) (w s))
      (∑ i : Fin 4, connectionSpeedPartials (m t) (u t) (v t) (w t) i * d i) t := by
  apply (hasDerivAt_connectionSpeed hm hu hv hw).congr_deriv
  simp [Fin.sum_univ_succ, connectionSpeedPartials]
  ring

theorem hasDerivAt_connectionPhaseB_weighted {m u v w : ℝ → ℝ} {t : ℝ} (d : Fin 4 → ℝ)
    (hm : HasDerivAt m (d 0 / matchingPhaseSlope (m t) (v t) (w t) +
      matchingPhaseVVariation (m t) (v t) (w t) * d 2 + matchingPhaseWVariation (m t) (v t) (w t) * d 3) t)
    (hu : HasDerivAt u (u t * d 1) t) (hv : HasDerivAt v (v t * d 2) t) (hw : HasDerivAt w (w t * d 3) t)
    (hmt : 1 < m t) (hD : connectionSpeed (m t) (u t) (v t) (w t) ≠ 0) :
    HasDerivAt (fun s => connectionPhaseB (m s) (u s) (v s) (w s))
      (∑ i : Fin 4, connectionPhaseBPartials (m t) (u t) (v t) (w t) i * d i) t := by
  have hR := hasDerivAt_matchingPhaseKernel_weighted d hm hv hw hmt
  have hd := hasDerivAt_connectionSpeed_weighted d hm hu hv hw
  have H : HasDerivAt (fun s => connectionPhaseB (m s) (u s) (v s) (w s))
      ((∑ i : Fin 4, matchingPhaseKernelPartials (m t) (v t) (w t) i * d i) /
          connectionSpeed (m t) (u t) (v t) (w t) -
        matchingPhaseKernel (m t) (v t) (w t) *
          (∑ i : Fin 4, connectionSpeedPartials (m t) (u t) (v t) (w t) i * d i) /
          connectionSpeed (m t) (u t) (v t) (w t) ^ 2) t := by
    apply (hR.div hd hD).congr_deriv
    field_simp
  apply H.congr_deriv
  simp [Fin.sum_univ_succ, connectionPhaseBPartials]
  ring

theorem hasDerivAt_connectionPhaseB_in_phase {M : MatchingPhaseParameters → ℝ}
    {p : MatchingPhaseParameters} {u : ℝ} (hM : DifferentiableAt ℝ M p) (hm : 1 < M p)
    (hf : matchingPhaseSlope (M p) (p 1) (p 2) ≠ 0)
    (heq : ∀ᶠ q in 𝓝 p, matchingPhase (M q) (q 1) (q 2) = q 0)
    (hD : connectionSpeed (M p) u (p 1) (p 2) ≠ 0) (d : Fin 4 → ℝ) :
    HasDerivAt (fun t => connectionPhaseB
      (M (matchingPhaseWeightedBase p ![d 0, d 2, d 3] t))
      (u * Real.exp (t * d 1)) (p 1 * Real.exp (t * d 2)) (p 2 * Real.exp (t * d 3)))
      (∑ i : Fin 4, connectionPhaseBPartials (M p) u (p 1) (p 2) i * d i) 0 := by
  have hexp (c k : ℝ) : HasDerivAt (fun t => c * Real.exp (t * k)) (c * k) 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).mul_const k).exp).const_mul c
  have hm' := hasDerivAt_matchingPhase_inverse_weighted hM hm hf heq ![d 0, d 2, d 3]
  have H := hasDerivAt_connectionPhaseB_weighted
    (m := fun t => M (matchingPhaseWeightedBase p ![d 0, d 2, d 3] t))
    (u := fun t => u * Real.exp (t * d 1))
    (v := fun t => p 1 * Real.exp (t * d 2))
    (w := fun t => p 2 * Real.exp (t * d 3)) (t := 0) d
    (by simpa [matchingPhaseWeightedBase_zero] using hm')
    (by simpa only [zero_mul, Real.exp_zero, mul_one] using hexp u (d 1))
    (by simpa only [zero_mul, Real.exp_zero, mul_one] using hexp (p 1) (d 2))
    (by simpa only [zero_mul, Real.exp_zero, mul_one] using hexp (p 2) (d 3))
    (by simpa only [matchingPhaseWeightedBase_zero] using hm)
    (by simpa only [matchingPhaseWeightedBase_zero, zero_mul, Real.exp_zero, mul_one] using hD)
  simpa only [matchingPhaseWeightedBase_zero, zero_mul, Real.exp_zero, mul_one] using H

end BianchiIX
