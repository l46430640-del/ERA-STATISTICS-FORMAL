import BianchiIX.Analysis.ConnectionPhaseDirection

noncomputable section

namespace BianchiIX

open Filter
open scoped Topology

def matchingPhaseSlopePartials (m v w : ℝ) : Fin 4 → ℝ :=
  ![matchingPhaseSlopeDm m v w / matchingPhaseSlope m v w, 0,
    -(m + 1) * v ^ 2 / phaseNorm (m + 1) v ^ 3 + matchingPhaseVVariation m v w * matchingPhaseSlopeDm m v w,
    -(m - 1) * w ^ 2 / phaseNorm (m - 1) w ^ 3 + matchingPhaseWVariation m v w * matchingPhaseSlopeDm m v w]

def matchingPhaseWeightPartials (m v w : ℝ) : Fin 4 → ℝ :=
  ![matchingPhaseWeightDm m v w / matchingPhaseSlope m v w, 0,
    (m + 1) * v ^ 2 / phaseNorm (m + 1) v ^ 3 +
      matchingPhaseVVariation m v w * (matchingPhaseWeightDm m v w - matchingPhaseSlope m v w),
    -(m - 1) * w ^ 2 / phaseNorm (m - 1) w ^ 3 +
      matchingPhaseWVariation m v w * (matchingPhaseWeightDm m v w - matchingPhaseSlope m v w)]

theorem hasDerivAt_matchingPhase_weighted {m v w : ℝ → ℝ} {t : ℝ} (d : Fin 4 → ℝ)
    (hm : HasDerivAt m (d 0 / matchingPhaseSlope (m t) (v t) (w t) +
      matchingPhaseVVariation (m t) (v t) (w t) * d 2 + matchingPhaseWVariation (m t) (v t) (w t) * d 3) t)
    (hv : HasDerivAt v (v t * d 2) t) (hw : HasDerivAt w (w t * d 3) t)
    (hmt : 1 < m t) (hf : matchingPhaseSlope (m t) (v t) (w t) ≠ 0) :
    HasDerivAt (fun s => matchingPhase (m s) (v s) (w s)) (d 0) t := by
  apply (hasDerivAt_matchingPhase hm hv hw hmt).congr_deriv
  dsimp [matchingPhaseVVariation, matchingPhaseWVariation]
  field_simp
  ring

theorem hasDerivAt_matchingPhaseSlope_weighted {m v w : ℝ → ℝ} {t : ℝ} (d : Fin 4 → ℝ)
    (hm : HasDerivAt m (d 0 / matchingPhaseSlope (m t) (v t) (w t) +
      matchingPhaseVVariation (m t) (v t) (w t) * d 2 + matchingPhaseWVariation (m t) (v t) (w t) * d 3) t)
    (hv : HasDerivAt v (v t * d 2) t) (hw : HasDerivAt w (w t * d 3) t) (hmt : 1 < m t) :
    HasDerivAt (fun s => matchingPhaseSlope (m s) (v s) (w s))
      (∑ i : Fin 4, matchingPhaseSlopePartials (m t) (v t) (w t) i * d i) t := by
  have hp := hasDerivAt_phaseNormRatio (hm.add_const 1) hv (by linarith only [hmt])
  have hn := hasDerivAt_phaseNormRatio (hm.sub_const 1) hw (by linarith only [hmt])
  apply ((hp.add hn).sub_const 1).congr_deriv
  simp [Fin.sum_univ_succ, matchingPhaseSlopePartials, matchingPhaseSlopeDm]
  ring

theorem hasDerivAt_matchingPhaseWeight_weighted {m v w : ℝ → ℝ} {t : ℝ} (d : Fin 4 → ℝ)
    (hm : HasDerivAt m (d 0 / matchingPhaseSlope (m t) (v t) (w t) +
      matchingPhaseVVariation (m t) (v t) (w t) * d 2 + matchingPhaseWVariation (m t) (v t) (w t) * d 3) t)
    (hv : HasDerivAt v (v t * d 2) t) (hw : HasDerivAt w (w t * d 3) t)
    (hmt : 1 < m t) (hf : matchingPhaseSlope (m t) (v t) (w t) ≠ 0) :
    HasDerivAt (fun s => matchingPhaseWeight (m s) (v s) (w s))
      (∑ i : Fin 4, matchingPhaseWeightPartials (m t) (v t) (w t) i * d i) t := by
  have hp := hasDerivAt_phaseNormRatio (hm.add_const 1) hv (by linarith only [hmt])
  have hn := hasDerivAt_phaseNormRatio (hm.sub_const 1) hw (by linarith only [hmt])
  have hF := hasDerivAt_matchingPhase_weighted d hm hv hw hmt hf
  have H := (hF.sub hp).add hn
  have heq : (fun s => matchingPhaseWeight (m s) (v s) (w s)) =ᶠ[𝓝 t]
      ((fun s => matchingPhase (m s) (v s) (w s)) - (fun s => (m s + 1) / phaseNorm (m s + 1) (v s)) +
        (fun s => (m s - 1) / phaseNorm (m s - 1) (w s))) := by
    filter_upwards [hm.continuousAt.eventually (eventually_gt_nhds hmt)] with s hs
    exact matchingPhaseWeight_identity hs
  apply (H.congr_of_eventuallyEq heq).congr_deriv
  simp [Fin.sum_univ_succ, matchingPhaseWeightPartials, matchingPhaseWeightDm]
  field_simp
  ring

end BianchiIX
