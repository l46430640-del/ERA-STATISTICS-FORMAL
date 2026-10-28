import BianchiIX.Analysis.MatchingPhaseWallDifferential

noncomputable section

namespace BianchiIX

def connectionPhaseNumerator (m u v w : ℝ) : ℝ :=
  matchingPhaseSlope m v w * (v - w) + (v + w - u) * matchingPhaseWeight m v w

def connectionPhaseNumeratorPartials (m u v w : ℝ) : Fin 4 → ℝ :=
  ![matchingPhaseSlopePartials m v w 0 * (v - w) + (v + w - u) * matchingPhaseWeightPartials m v w 0,
    -u * matchingPhaseWeight m v w,
    matchingPhaseSlopePartials m v w 2 * (v - w) + matchingPhaseSlope m v w * v +
      v * matchingPhaseWeight m v w + (v + w - u) * matchingPhaseWeightPartials m v w 2,
    matchingPhaseSlopePartials m v w 3 * (v - w) - matchingPhaseSlope m v w * w +
      w * matchingPhaseWeight m v w + (v + w - u) * matchingPhaseWeightPartials m v w 3]

def connectionPhaseAPartials (m u v w : ℝ) (i : Fin 4) : ℝ :=
  -connectionPhaseNumeratorPartials m u v w i / connectionSpeed m u v w -
    connectionPhaseA m u v w * connectionSpeedPartials m u v w i / connectionSpeed m u v w

theorem connectionPhaseAPartials_phase {m u v w : ℝ} (hD : connectionSpeed m u v w ≠ 0) :
    connectionPhaseAPartials m u v w 0 = connectionPhaseAJ m u v w := by
  dsimp [connectionPhaseAPartials, connectionPhaseNumeratorPartials, matchingPhaseSlopePartials,
    matchingPhaseWeightPartials, connectionSpeedPartials, connectionPhaseAJ,
    connectionPhaseRemainderDm, connectionPhaseRemainder, connectionPhaseA]
  field_simp
  ring

theorem hasDerivAt_connectionPhaseNumerator_weighted {m u v w : ℝ → ℝ} {t : ℝ} (d : Fin 4 → ℝ)
    (hm : HasDerivAt m (d 0 / matchingPhaseSlope (m t) (v t) (w t) +
      matchingPhaseVVariation (m t) (v t) (w t) * d 2 + matchingPhaseWVariation (m t) (v t) (w t) * d 3) t)
    (hu : HasDerivAt u (u t * d 1) t) (hv : HasDerivAt v (v t * d 2) t) (hw : HasDerivAt w (w t * d 3) t)
    (hmt : 1 < m t) (hf : matchingPhaseSlope (m t) (v t) (w t) ≠ 0) :
    HasDerivAt (fun s => connectionPhaseNumerator (m s) (u s) (v s) (w s))
      (∑ i : Fin 4, connectionPhaseNumeratorPartials (m t) (u t) (v t) (w t) i * d i) t := by
  have hF := hasDerivAt_matchingPhaseSlope_weighted d hm hv hw hmt
  have hH := hasDerivAt_matchingPhaseWeight_weighted d hm hv hw hmt hf
  apply ((hF.mul (hv.sub hw)).add (((hv.add hw).sub hu).mul hH)).congr_deriv
  simp [Fin.sum_univ_succ, connectionPhaseNumeratorPartials, matchingPhaseSlopePartials,
    matchingPhaseWeightPartials, Pi.sub_apply, Pi.add_apply]
  ring

theorem hasDerivAt_connectionPhaseA_weighted {m u v w : ℝ → ℝ} {t : ℝ} (d : Fin 4 → ℝ)
    (hm : HasDerivAt m (d 0 / matchingPhaseSlope (m t) (v t) (w t) +
      matchingPhaseVVariation (m t) (v t) (w t) * d 2 + matchingPhaseWVariation (m t) (v t) (w t) * d 3) t)
    (hu : HasDerivAt u (u t * d 1) t) (hv : HasDerivAt v (v t * d 2) t) (hw : HasDerivAt w (w t * d 3) t)
    (hmt : 1 < m t) (hf : matchingPhaseSlope (m t) (v t) (w t) ≠ 0)
    (hD : connectionSpeed (m t) (u t) (v t) (w t) ≠ 0) :
    HasDerivAt (fun s => connectionPhaseA (m s) (u s) (v s) (w s))
      (∑ i : Fin 4, connectionPhaseAPartials (m t) (u t) (v t) (w t) i * d i) t := by
  have hN := hasDerivAt_connectionPhaseNumerator_weighted d hm hu hv hw hmt hf
  have hd := hasDerivAt_connectionSpeed_weighted d hm hu hv hw
  have H : HasDerivAt (fun s => connectionPhaseA (m s) (u s) (v s) (w s))
      (-(∑ i : Fin 4, connectionPhaseNumeratorPartials (m t) (u t) (v t) (w t) i * d i) /
        connectionSpeed (m t) (u t) (v t) (w t) -
        connectionPhaseA (m t) (u t) (v t) (w t) *
          (∑ i : Fin 4, connectionSpeedPartials (m t) (u t) (v t) (w t) i * d i) /
          connectionSpeed (m t) (u t) (v t) (w t)) t := by
    apply (hN.neg.div hd hD).congr_deriv
    dsimp [connectionPhaseA, connectionPhaseNumerator]
    field_simp
  apply H.congr_deriv
  simp [Fin.sum_univ_succ, connectionPhaseAPartials]
  ring

end BianchiIX
