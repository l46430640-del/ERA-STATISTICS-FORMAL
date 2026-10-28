import BianchiIX.Analysis.MatchingPhaseWeight

noncomputable section

namespace BianchiIX

open Filter
open scoped Topology

theorem hasDerivAt_phaseNormRatio {a b : ℝ → ℝ} {a' b' t : ℝ}
    (ha : HasDerivAt a a' t) (hb : HasDerivAt b b' t) (ha0 : 0 < a t) :
    HasDerivAt (fun s => a s / phaseNorm (a s) (b s))
      ((b t ^ 2 * a' - a t * b t * b') / phaseNorm (a t) (b t) ^ 3) t := by
  have hK := phaseNorm_pos (b := b t) ha0
  apply (ha.div (hasDerivAt_phaseNorm ha hb ha0) (ne_of_gt hK)).congr_deriv
  field_simp
  linear_combination a' * phaseNorm_sq (a t) (b t)

def matchingPhaseSlopeDm (m v w : ℝ) : ℝ :=
  v ^ 2 / phaseNorm (m + 1) v ^ 3 + w ^ 2 / phaseNorm (m - 1) w ^ 3

def matchingPhaseWeightDm (m v w : ℝ) : ℝ :=
  matchingPhaseSlope m v w - v ^ 2 / phaseNorm (m + 1) v ^ 3 + w ^ 2 / phaseNorm (m - 1) w ^ 3

theorem hasDerivAt_matchingPhaseSlope_m {m v w : ℝ} (hm : 1 < m) :
    HasDerivAt (fun s => matchingPhaseSlope s v w) (matchingPhaseSlopeDm m v w) m := by
  have hp := hasDerivAt_phaseNormRatio ((hasDerivAt_id m).add_const 1) (hasDerivAt_const m v)
    (by simpa using (show 0 < m + 1 by linarith only [hm]))
  have hn := hasDerivAt_phaseNormRatio ((hasDerivAt_id m).sub_const 1) (hasDerivAt_const m w)
    (by simpa using (show 0 < m - 1 by linarith only [hm]))
  simpa [matchingPhaseSlope, matchingPhaseSlopeDm] using (hp.add hn).sub_const 1

theorem hasDerivAt_matchingPhaseWeight_m {m v w : ℝ} (hm : 1 < m) :
    HasDerivAt (fun s => matchingPhaseWeight s v w) (matchingPhaseWeightDm m v w) m := by
  have hp := hasDerivAt_phaseNormRatio ((hasDerivAt_id m).add_const 1) (hasDerivAt_const m v)
    (by simpa using (show 0 < m + 1 by linarith only [hm]))
  have hn := hasDerivAt_phaseNormRatio ((hasDerivAt_id m).sub_const 1) (hasDerivAt_const m w)
    (by simpa using (show 0 < m - 1 by linarith only [hm]))
  have hF := hasDerivAt_matchingPhase (hasDerivAt_id m) (hasDerivAt_const m v) (hasDerivAt_const m w) hm
  have H : HasDerivAt (fun s => matchingPhase s v w - (s + 1) / phaseNorm (s + 1) v +
      (s - 1) / phaseNorm (s - 1) w) (matchingPhaseWeightDm m v w) m := by
    simpa [matchingPhaseWeightDm, Pi.add_def, Pi.sub_def] using (hF.sub hp).add hn
  apply H.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hm] with s hs
  exact matchingPhaseWeight_identity hs

def connectionPhaseRemainderDm (m u v w : ℝ) : ℝ :=
  matchingPhaseSlopeDm m v w * (v - w) + (v + w - u) * (matchingPhaseWeightDm m v w - 1)

theorem hasDerivAt_connectionPhaseRemainder_m {m u v w : ℝ} (hm : 1 < m) :
    HasDerivAt (fun s => connectionPhaseRemainder s u v w) (connectionPhaseRemainderDm m u v w) m := by
  have hD : HasDerivAt (fun s => connectionSpeed s u v w) 1 m :=
    ((hasDerivAt_id m).sub_const 1).sub_const (coupling u v w)
  exact ((hasDerivAt_matchingPhaseSlope_m hm).mul_const (v - w)).add
    (((hasDerivAt_matchingPhaseWeight_m hm).sub hD).const_mul (v + w - u))

theorem hasDerivAt_connectionPhaseA_m {m u v w : ℝ} (hm : 1 < m)
    (hD : connectionSpeed m u v w ≠ 0) :
    HasDerivAt (fun s => connectionPhaseA s u v w)
      (-connectionPhaseRemainderDm m u v w / connectionSpeed m u v w +
        connectionPhaseRemainder m u v w / connectionSpeed m u v w ^ 2) m := by
  have hden : HasDerivAt (fun s => connectionSpeed s u v w) 1 m :=
    ((hasDerivAt_id m).sub_const 1).sub_const (coupling u v w)
  have hnum := ((hasDerivAt_matchingPhaseSlope_m (v := v) (w := w) hm).mul_const (v - w)).add
    ((hasDerivAt_matchingPhaseWeight_m (v := v) (w := w) hm).const_mul (v + w - u))
  apply (hnum.neg.div hden hD).congr_deriv
  dsimp [connectionPhaseRemainderDm, connectionPhaseRemainder]
  field_simp
  ring

end BianchiIX
