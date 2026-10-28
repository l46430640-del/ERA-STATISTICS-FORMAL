import BianchiIX.Analysis.MatchingPhaseAuxiliaryBounds

noncomputable section

namespace BianchiIX

open Filter
open scoped Topology

def connectionPhaseAJ (m u v w : ℝ) : ℝ :=
  (-connectionPhaseRemainderDm m u v w / connectionSpeed m u v w +
    connectionPhaseRemainder m u v w / connectionSpeed m u v w ^ 2) / matchingPhaseSlope m v w

def connectionPhaseGJ (m u v w : ℝ) : ℝ :=
  u * connectionPhaseAJ m u v w + (v * w) ^ 2 * connectionPhaseBPartials m u v w 0

theorem hasDerivAt_connectionPhaseA_in_phase {M : MatchingPhaseParameters → ℝ}
    {p : MatchingPhaseParameters} {u : ℝ} (hM : DifferentiableAt ℝ M p) (hm : 1 < M p)
    (hf : matchingPhaseSlope (M p) (p 1) (p 2) ≠ 0)
    (heq : ∀ᶠ q in 𝓝 p, matchingPhase (M q) (q 1) (q 2) = q 0)
    (hD : connectionSpeed (M p) u (p 1) (p 2) ≠ 0) :
    HasDerivAt (fun t => connectionPhaseA (M ![p 0 + t, p 1, p 2]) u (p 1) (p 2))
      (connectionPhaseAJ (M p) u (p 1) (p 2)) 0 := by
  have hinner : HasDerivAt (fun t => M ![p 0 + t, p 1, p 2])
      (1 / matchingPhaseSlope (M p) (p 1) (p 2)) 0 := by
    simpa [matchingPhaseWeightedBase] using hasDerivAt_matchingPhase_inverse_weighted hM hm hf heq ![1, 0, 0]
  have hseed : (![p 0 + 0, p 1, p 2] : MatchingPhaseParameters) = p := by
    ext i
    fin_cases i <;> simp
  have houter : HasDerivAt (fun s => connectionPhaseA s u (p 1) (p 2))
      (-connectionPhaseRemainderDm (M p) u (p 1) (p 2) / connectionSpeed (M p) u (p 1) (p 2) +
        connectionPhaseRemainder (M p) u (p 1) (p 2) / connectionSpeed (M p) u (p 1) (p 2) ^ 2)
      (M ![p 0 + 0, p 1, p 2]) := by
    rw [hseed]
    exact hasDerivAt_connectionPhaseA_m hm hD
  apply (houter.comp 0 hinner).congr_deriv
  dsimp [connectionPhaseAJ]
  ring

theorem hasDerivAt_connectionPhaseG_in_phase {M : MatchingPhaseParameters → ℝ}
    {p : MatchingPhaseParameters} {u : ℝ} (hM : DifferentiableAt ℝ M p) (hm : 1 < M p)
    (hf : matchingPhaseSlope (M p) (p 1) (p 2) ≠ 0)
    (heq : ∀ᶠ q in 𝓝 p, matchingPhase (M q) (q 1) (q 2) = q 0)
    (hD : connectionSpeed (M p) u (p 1) (p 2) ≠ 0) :
    HasDerivAt (fun t => connectionPhaseG (M ![p 0 + t, p 1, p 2]) u (p 1) (p 2))
      (connectionPhaseGJ (M p) u (p 1) (p 2)) 0 := by
  have hA := hasDerivAt_connectionPhaseA_in_phase hM hm hf heq hD
  have hB : HasDerivAt (fun t => connectionPhaseB (M ![p 0 + t, p 1, p 2]) u (p 1) (p 2))
      (connectionPhaseBPartials (M p) u (p 1) (p 2) 0) 0 := by
    simpa [Fin.sum_univ_succ, matchingPhaseWeightedBase] using
      hasDerivAt_connectionPhaseB_in_phase hM hm hf heq hD ![1, 0, 0, 0]
  convert! (hA.const_mul u).add (hB.const_mul ((p 1 * p 2) ^ 2)) using 1
  ext t
  exact connectionPhaseG_decomposition _ _ _ _

theorem connectionPhaseAJ_bound {μ m u v w : ℝ} (hμ : 4 ≤ μ)
    (hm : |m - μ| ≤ 1 / 2) (hu : 0 ≤ u ∧ u ≤ 1 / 10000)
    (hv : 0 ≤ v ∧ v ≤ 1) (hw : 0 ≤ w ∧ w ≤ 1) :
    |connectionPhaseAJ m u v w| ≤ 48 / μ ^ 2 := by
  have hμ0 : 0 < μ := by linarith only [hμ]
  have hμne := ne_of_gt hμ0
  have hD := (connection_speed_bounds hμ hm hu hv hw).1
  have hD0 : 0 < connectionSpeed m u v w := by linarith only [hD, hμ0]
  have hD2 : μ ^ 2 / 4 ≤ connectionSpeed m u v w ^ 2 := by
    have H := pow_le_pow_left₀ (by positivity : 0 ≤ μ / 2) hD 2
    nlinarith only [H]
  have hN := connectionPhaseRemainder_bound hμ hm hu hv hw
  have hNJ := connectionPhaseRemainder_phase_bound hμ hm hu hv hw
  have hf := (matchingPhase_inverse_weighted_bounds hμ hm hv hw).1
  have hfirst : |(connectionPhaseRemainderDm m u v w / matchingPhaseSlope m v w) /
      connectionSpeed m u v w| ≤ 40 / μ ^ 3 := by
    rw [abs_div, abs_of_pos hD0]
    exact (div_le_div₀ (by positivity) hNJ (by positivity) hD).trans_eq (by ring)
  have hsecond : |(connectionPhaseRemainder m u v w * (1 / matchingPhaseSlope m v w)) /
      connectionSpeed m u v w ^ 2| ≤ 32 / μ ^ 2 := by
    have H : |connectionPhaseRemainder m u v w * (1 / matchingPhaseSlope m v w)| ≤ 8 := by
      rw [abs_mul]
      exact (mul_le_mul hN hf (abs_nonneg _) (by norm_num)).trans_eq (by norm_num)
    rw [abs_div, abs_of_pos (pow_pos hD0 2)]
    exact (div_le_div₀ (by norm_num) H (by positivity) hD2).trans_eq (by ring)
  have hid : connectionPhaseAJ m u v w =
      -((connectionPhaseRemainderDm m u v w / matchingPhaseSlope m v w) / connectionSpeed m u v w) +
      (connectionPhaseRemainder m u v w * (1 / matchingPhaseSlope m v w)) / connectionSpeed m u v w ^ 2 := by
    dsimp [connectionPhaseAJ]
    ring
  rw [hid]
  have H := abs_add_le (-((connectionPhaseRemainderDm m u v w / matchingPhaseSlope m v w) /
    connectionSpeed m u v w)) ((connectionPhaseRemainder m u v w * (1 / matchingPhaseSlope m v w)) / connectionSpeed m u v w ^ 2)
  rw [abs_neg] at H
  calc
    _ ≤ 40 / μ ^ 3 + 32 / μ ^ 2 := H.trans (add_le_add hfirst hsecond)
    _ = (40 + 32 * μ) / μ ^ 3 := by field_simp
    _ ≤ (48 * μ) / μ ^ 3 := div_le_div_of_nonneg_right (by linarith only [hμ]) (by positivity)
    _ = 48 / μ ^ 2 := by field_simp

theorem connectionPhaseGJ_bound {μ m u v w : ℝ} (hμ : 4 ≤ μ)
    (hm : |m - μ| ≤ 1 / 2) (hu : 0 ≤ u ∧ u ≤ 1 / 10000)
    (hv : 0 ≤ v ∧ v ≤ 1) (hw : 0 ≤ w ∧ w ≤ 1) :
    |connectionPhaseGJ m u v w| ≤ 64 * (u / μ ^ 2 + (v * w) ^ 2 / μ ^ 4) := by
  have hμ0 : 0 < μ := by linarith only [hμ]
  have hA := connectionPhaseAJ_bound hμ hm hu hv hw
  have hB := (connectionPhaseB_bounds hμ hm hu hv hw).2.1
  have H1 : |u * connectionPhaseAJ m u v w| ≤ u * (48 / μ ^ 2) := by
    rw [abs_mul, abs_of_nonneg hu.1]
    exact mul_le_mul_of_nonneg_left hA hu.1
  have H2 : |(v * w) ^ 2 * connectionPhaseBPartials m u v w 0| ≤ (v * w) ^ 2 * (40 / μ ^ 4) := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
    exact mul_le_mul_of_nonneg_left hB (sq_nonneg _)
  apply ((abs_add_le _ _).trans (add_le_add H1 H2)).trans
  have huq : 0 ≤ u / μ ^ 2 := div_nonneg hu.1 (sq_nonneg μ)
  have hpq : 0 ≤ (v * w) ^ 2 / μ ^ 4 := by positivity
  calc
    _ = 48 * (u / μ ^ 2) + 40 * ((v * w) ^ 2 / μ ^ 4) := by ring
    _ ≤ 64 * (u / μ ^ 2 + (v * w) ^ 2 / μ ^ 4) := by linarith only [huq, hpq]

end BianchiIX
