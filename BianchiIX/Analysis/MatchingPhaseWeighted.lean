import BianchiIX.Analysis.MatchingPhaseChart
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

noncomputable section

namespace BianchiIX

open Filter
open scoped Topology

def matchingPhaseVVariation (m v w : ℝ) : ℝ :=
  -v ^ 2 / (phaseNorm (m + 1) v * matchingPhaseSlope m v w)

def matchingPhaseWVariation (m v w : ℝ) : ℝ :=
  -w ^ 2 / (phaseNorm (m - 1) w * matchingPhaseSlope m v w)

/-- Multiplicative wall variations give the logarithmic directions, including their zero-wall extension. -/
def matchingPhaseWeightedBase (p d : MatchingPhaseParameters) (t : ℝ) : MatchingPhaseParameters :=
  ![p 0 + t * d 0, p 1 * Real.exp (t * d 1), p 2 * Real.exp (t * d 2)]

theorem matchingPhaseWeightedBase_zero (p d : MatchingPhaseParameters) :
    matchingPhaseWeightedBase p d 0 = p := by
  ext i
  fin_cases i <;> simp [matchingPhaseWeightedBase]

theorem hasDerivAt_matchingPhaseWeightedBase (p d : MatchingPhaseParameters) :
    HasDerivAt (matchingPhaseWeightedBase p d) ![d 0, p 1 * d 1, p 2 * d 2] 0 := by
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · simpa [matchingPhaseWeightedBase] using ((hasDerivAt_id (0 : ℝ)).mul_const (d 0)).const_add (p 0)
  · simpa [matchingPhaseWeightedBase] using (((hasDerivAt_id (0 : ℝ)).mul_const (d 1)).exp).const_mul (p 1)
  · simpa [matchingPhaseWeightedBase] using (((hasDerivAt_id (0 : ℝ)).mul_const (d 2)).exp).const_mul (p 2)

theorem hasDerivAt_matchingPhase_inverse_weighted {M : MatchingPhaseParameters → ℝ}
    {p : MatchingPhaseParameters} (hM : DifferentiableAt ℝ M p) (hm : 1 < M p)
    (hf : matchingPhaseSlope (M p) (p 1) (p 2) ≠ 0)
    (heq : ∀ᶠ q in 𝓝 p, matchingPhase (M q) (q 1) (q 2) = q 0) (d : MatchingPhaseParameters) :
    HasDerivAt (fun t => M (matchingPhaseWeightedBase p d t))
      (d 0 / matchingPhaseSlope (M p) (p 1) (p 2) +
        matchingPhaseVVariation (M p) (p 1) (p 2) * d 1 +
        matchingPhaseWVariation (M p) (p 1) (p 2) * d 2) 0 := by
  have hd := (matchingPhaseWeightedBase_zero p d).symm ▸ hM.hasFDerivAt
  have H := hd.comp_hasDerivAt 0 (hasDerivAt_matchingPhaseWeightedBase p d)
  apply H.congr_deriv
  rw [matchingPhaseWeightedBase_zero, matchingPhase_inverse_fderiv hM hm hf heq]
  dsimp [matchingPhaseVVariation, matchingPhaseWVariation]
  ring

theorem matchingPhase_inverse_weighted_bounds {μ m v w : ℝ} (hμ : 4 ≤ μ)
    (hm : |m - μ| ≤ 1 / 2) (hv : 0 ≤ v ∧ v ≤ 1) (hw : 0 ≤ w ∧ w ≤ 1) :
    |1 / matchingPhaseSlope m v w| ≤ 4 / 3 ∧
      |matchingPhaseVVariation m v w| ≤ 3 * v ^ 2 / μ ∧
      |matchingPhaseWVariation m v w| ≤ 3 * w ^ 2 / μ := by
  have hμ0 : 0 < μ := by linarith only [hμ]
  have hf := (matchingPhase_slope_bounds hμ hm hv hw).1
  have hf0 : 0 < matchingPhaseSlope m v w := by linarith only [hf]
  have hp := phaseNorm_ge (b := v) (show 0 ≤ m + 1 by linarith only [hμ, (abs_le.mp hm).1])
  have hn := phaseNorm_ge (b := w) (show 0 ≤ m - 1 by linarith only [hμ, (abs_le.mp hm).1])
  have bound (K r : ℝ) (hK : μ / 2 ≤ K) : |(-r ^ 2) / (K * matchingPhaseSlope m v w)| ≤ 3 * r ^ 2 / μ := by
    have hK0 : 0 < K := by linarith only [hK, hμ0]
    have hprod : μ / 3 ≤ K * matchingPhaseSlope m v w := by
      have H := mul_le_mul hK hf (by norm_num : (0 : ℝ) ≤ 3 / 4) hK0.le
      nlinarith only [H, hμ0]
    rw [abs_div, abs_neg, abs_of_nonneg (sq_nonneg r), abs_of_pos (mul_pos hK0 hf0)]
    exact (div_le_div_of_nonneg_left (sq_nonneg r) (by positivity) hprod).trans_eq (by ring)
  refine ⟨?_, bound _ v (by linarith only [hp, hμ, (abs_le.mp hm).1]),
    bound _ w (by linarith only [hn, hμ, (abs_le.mp hm).1])⟩
  rw [abs_of_pos (by positivity : 0 < 1 / matchingPhaseSlope m v w)]
  exact (div_le_iff₀ hf0).mpr (by linarith only [hf])

end BianchiIX
