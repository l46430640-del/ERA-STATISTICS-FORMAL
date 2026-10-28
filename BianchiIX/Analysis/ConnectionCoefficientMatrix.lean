import BianchiIX.Analysis.ConnectionPhaseWallBounds
import BianchiIX.Analysis.ConnectionAmplitudeCoordinates

noncomputable section

namespace BianchiIX

open Filter
open scoped Topology

def connectionLogRates (m u v w : ℝ) : Fin 3 → ℝ :=
  ![connectionPhaseG m u v w, connectionStrongClockRate m u v w, connectionWeakClockRate m u v w]

/-- Rows are G, a, b; columns are J, log U, log V, log W. -/
def connectionLogCoefficientMatrix (m u v w : ℝ) : Fin 3 → Fin 4 → ℝ :=
  ![connectionPhaseGPartials m u v w, connectionStrongClockPartials m u v w, connectionWeakClockPartials m u v w]

def connectionLogCoefficientScales (μ u v w : ℝ) : Fin 3 → Fin 4 → ℝ :=
  ![![u / μ ^ 2 + (v * w) ^ 2 / μ ^ 4, u, u * v + (v * w) ^ 2 / μ ^ 3, u * w + (v * w) ^ 2 / μ ^ 3],
    ![1, u, (v ^ 2 + v * w) / μ + u * v, (w ^ 2 + v * w) / μ + u * w],
    ![1 / μ ^ 2, u / μ, v ^ 2 / μ ^ 3 + u * v / μ, w ^ 2 / μ ^ 3 + u * w / μ]]

theorem connectionLogCoefficientMatrix_bound {μ m u v w : ℝ} (hμ : 4 ≤ μ)
    (hm : |m - μ| ≤ 1 / 2) (hu : 0 ≤ u ∧ u ≤ 1 / 10000)
    (hv : 0 ≤ v ∧ v ≤ 1) (hw : 0 ≤ w ∧ w ≤ 1) :
    ∀ i j, |connectionLogCoefficientMatrix m u v w i j| ≤ 64 * connectionLogCoefficientScales μ u v w i j := by
  have hG := connectionPhaseGPartials_bounds hμ hm hu hv hw
  have ha := connectionStrongClockPartials_bounds hμ hm hu hv hw
  have hb := connectionWeakClockPartials_bounds hμ hm hu hv hw
  have weaken {x s : ℝ} (hx : |x| ≤ 32 * s) : |x| ≤ 64 * s := by
    have hs : 0 ≤ s := by linarith only [hx, abs_nonneg x]
    linarith only [hx, hs]
  intro i j
  fin_cases i <;> fin_cases j
  · change |connectionPhaseGPartials m u v w 0| ≤ 64 * (u / μ ^ 2 + (v * w) ^ 2 / μ ^ 4)
    exact hG.1
  · change |connectionPhaseGPartials m u v w 1| ≤ 64 * u
    exact weaken hG.2.1
  · change |connectionPhaseGPartials m u v w 2| ≤ 64 * (u * v + (v * w) ^ 2 / μ ^ 3)
    exact weaken hG.2.2.1
  · change |connectionPhaseGPartials m u v w 3| ≤ 64 * (u * w + (v * w) ^ 2 / μ ^ 3)
    exact weaken hG.2.2.2
  · change |connectionStrongClockPartials m u v w 0| ≤ 64 * 1
    exact ha.1.trans (by norm_num)
  · change |connectionStrongClockPartials m u v w 1| ≤ 64 * u
    exact weaken ha.2.1
  · change |connectionStrongClockPartials m u v w 2| ≤ 64 * ((v ^ 2 + v * w) / μ + u * v)
    exact weaken ha.2.2.1
  · change |connectionStrongClockPartials m u v w 3| ≤ 64 * ((w ^ 2 + v * w) / μ + u * w)
    exact weaken ha.2.2.2
  · change |connectionWeakClockPartials m u v w 0| ≤ 64 * (1 / μ ^ 2)
    exact hb.1.trans_eq (by ring)
  · change |connectionWeakClockPartials m u v w 1| ≤ 64 * (u / μ)
    exact hb.2.1.trans_eq (by ring)
  · change |connectionWeakClockPartials m u v w 2| ≤ 64 * (v ^ 2 / μ ^ 3 + u * v / μ)
    exact hb.2.2.1
  · change |connectionWeakClockPartials m u v w 3| ≤ 64 * (w ^ 2 / μ ^ 3 + u * w / μ)
    exact hb.2.2.2

theorem hasDerivAt_connectionLogRates_weighted {m u v w : ℝ → ℝ} {t : ℝ} (d : Fin 4 → ℝ)
    (hm : HasDerivAt m (d 0 / matchingPhaseSlope (m t) (v t) (w t) +
      matchingPhaseVVariation (m t) (v t) (w t) * d 2 + matchingPhaseWVariation (m t) (v t) (w t) * d 3) t)
    (hu : HasDerivAt u (u t * d 1) t) (hv : HasDerivAt v (v t * d 2) t) (hw : HasDerivAt w (w t * d 3) t)
    (hmt : 1 < m t) (hf : matchingPhaseSlope (m t) (v t) (w t) ≠ 0)
    (hD : connectionSpeed (m t) (u t) (v t) (w t) ≠ 0) :
    HasDerivAt (fun s => connectionLogRates (m s) (u s) (v s) (w s))
      (fun i => ∑ j : Fin 4, connectionLogCoefficientMatrix (m t) (u t) (v t) (w t) i j * d j) t := by
  have hG := hasDerivAt_connectionPhaseG_weighted d hm hu hv hw hmt hf hD
  have hab := hasDerivAt_connection_clock_weighted_curves d hm hu hv hw hD
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · exact hG
  · exact hab.1
  · exact hab.2

theorem hasDerivAt_connectionLogRates_in_phase {M : MatchingPhaseParameters → ℝ}
    {p : MatchingPhaseParameters} {u : ℝ} (hM : DifferentiableAt ℝ M p) (hm : 1 < M p)
    (hf : matchingPhaseSlope (M p) (p 1) (p 2) ≠ 0)
    (heq : ∀ᶠ q in 𝓝 p, matchingPhase (M q) (q 1) (q 2) = q 0)
    (hD : connectionSpeed (M p) u (p 1) (p 2) ≠ 0) (d : Fin 4 → ℝ) :
    HasDerivAt (fun t => connectionLogRates
      (M (matchingPhaseWeightedBase p ![d 0, d 2, d 3] t))
      (u * Real.exp (t * d 1)) (p 1 * Real.exp (t * d 2)) (p 2 * Real.exp (t * d 3)))
      (fun i => ∑ j : Fin 4, connectionLogCoefficientMatrix (M p) u (p 1) (p 2) i j * d j) 0 := by
  have hG := hasDerivAt_connectionPhaseG_weighted_in_phase hM hm hf heq hD d
  have hab := hasDerivAt_connection_clock_in_phase hM hm hf heq hD d
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · exact hG
  · exact hab.1
  · exact hab.2

theorem exists_connection_coefficient_chart {μ m u v w : ℝ} (hμ : 4 ≤ μ)
    (hm : |m - μ| ≤ 1 / 2) (hu : 0 ≤ u ∧ u ≤ 1 / 10000)
    (hv : 0 ≤ v ∧ v ≤ 1) (hw : 0 ≤ w ∧ w ≤ 1) :
    let p := matchingPhaseSeed m v w
    ∃ M : MatchingPhaseParameters → ℝ, M p = m ∧ ContDiffAt ℝ 2 M p ∧
      (∀ᶠ q in 𝓝 p, matchingPhase (M q) (q 1) (q 2) = q 0) ∧
      (∀ d : Fin 4 → ℝ, HasDerivAt (fun t => connectionLogRates
        (M (matchingPhaseWeightedBase p ![d 0, d 2, d 3] t))
        (u * Real.exp (t * d 1)) (v * Real.exp (t * d 2)) (w * Real.exp (t * d 3)))
        (fun i => ∑ j : Fin 4, connectionLogCoefficientMatrix m u v w i j * d j) 0) ∧
      (∀ i j, |connectionLogCoefficientMatrix m u v w i j| ≤ 64 * connectionLogCoefficientScales μ u v w i j) := by
  intro p
  obtain ⟨M, hMp, hCM, heq, _, _⟩ := exists_matchingPhase_chart hμ hm hv hw
  have hp1 : p 1 = v := rfl
  have hp2 : p 2 = w := rfl
  have hm1 : 1 < M p := by rw [hMp]; linarith only [hμ, (abs_le.mp hm).1]
  have hf : matchingPhaseSlope (M p) (p 1) (p 2) ≠ 0 := by
    rw [hMp, hp1, hp2]
    have H := (matchingPhase_slope_bounds hμ hm hv hw).1
    linarith only [H]
  have hD : connectionSpeed (M p) u (p 1) (p 2) ≠ 0 := by
    rw [hMp, hp1, hp2]
    have H := (connection_speed_bounds hμ hm hu hv hw).1
    linarith only [H, hμ]
  refine ⟨M, hMp, hCM, heq, ?_, connectionLogCoefficientMatrix_bound hμ hm hu hv hw⟩
  intro d
  have hseed1 : matchingPhaseSeed m v w 1 = v := rfl
  have hseed2 : matchingPhaseSeed m v w 2 = w := rfl
  simpa only [hMp, hseed1, hseed2] using
    hasDerivAt_connectionLogRates_in_phase (hCM.differentiableAt (by norm_num)) hm1 hf heq hD d

end BianchiIX
