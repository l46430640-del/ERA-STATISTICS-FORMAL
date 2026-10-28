import BianchiIX.Analysis.ConnectionLogLinearization
import BianchiIX.Analysis.ConnectionTransverseCoefficients

noncomputable section

namespace BianchiIX

def connectionWeightedTangent (μ : ℝ) (d : Fin 4 → ℝ) : Fin 2 → ℝ := ![d 1, μ ^ 2 * d 2]

def connectionPhaseColumn (μ : ℝ) (y : ProjectiveState) : Fin 2 → ℝ :=
  ![connectionStrongClockPartials (-y 0) (y 1) (y 2) (y 3) 0,
    μ ^ 2 * connectionWeakClockPartials (-y 0) (y 1) (y 2) (y 3) 0]

def connectionWallColumn (μ : ℝ) (y : ProjectiveState) : Fin 2 → ℝ :=
  ![connectionStrongClockPartials (-y 0) (y 1) (y 2) (y 3) 3,
    μ ^ 2 * connectionWeakClockPartials (-y 0) (y 1) (y 2) (y 3) 3]

theorem connectionWeightedTangent_linearized {μ : ℝ} (hμ : μ ≠ 0) (y : ProjectiveState) (d : Fin 4 → ℝ) :
    connectionWeightedTangent μ (connectionLogLinearizedRates y d) =
      (connectionTransverseMatrix μ (-y 0) (y 1) (y 2) (y 3)).mulVec (connectionWeightedTangent μ d) +
        d 0 • connectionPhaseColumn μ y + d 3 • connectionWallColumn μ y := by
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  let a := connectionStrongClockPartials (-y 0) (y 1) (y 2) (y 3)
  let b := connectionWeakClockPartials (-y 0) (y 1) (y 2) (y 3)
  fin_cases i
  · change (∑ j : Fin 4, a j * d j) = a 1 * d 1 + a 2 / μ ^ 2 * (μ ^ 2 * d 2) + d 0 * a 0 + d 3 * a 3
    simp [Fin.sum_univ_succ]
    field_simp
    ring
  · change μ ^ 2 * (∑ j : Fin 4, b j * d j) =
      (μ ^ 2 * b 1) * d 1 + b 2 * (μ ^ 2 * d 2) + d 0 * (μ ^ 2 * b 0) + d 3 * (μ ^ 2 * b 3)
    simp [Fin.sum_univ_succ]
    ring

theorem hasDerivAt_connectionWeightedTangent {D : ℝ → (Fin 4 → ℝ)} {Y : ℝ → ProjectiveState} {μ t : ℝ}
    (hμ : μ ≠ 0) (hD : HasDerivAt D (connectionLogLinearizedRates (Y t) (D t)) t) :
    HasDerivAt (fun s => connectionWeightedTangent μ (D s))
      ((connectionTransverseMatrix μ (-Y t 0) (Y t 1) (Y t 2) (Y t 3)).mulVec (connectionWeightedTangent μ (D t)) +
        D t 0 • connectionPhaseColumn μ (Y t) + D t 3 • connectionWallColumn μ (Y t)) t := by
  rw [← connectionWeightedTangent_linearized hμ]
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · exact hasDerivAt_pi.mp hD 1
  · exact (hasDerivAt_pi.mp hD 2).const_mul (μ ^ 2)

theorem connectionPhaseColumn_norm {μ : ℝ} {y : ProjectiveState} (hμ : 4 ≤ μ)
    (hm : |-y 0 - μ| ≤ 1 / 2) (hu : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000)
    (hv : 0 ≤ y 2 ∧ y 2 ≤ 1) (hw : 0 ≤ y 3 ∧ y 3 ≤ 1) :
    ‖connectionPhaseColumn μ y‖ ≤ 64 := by
  have hμ0 : 0 < μ := by linarith only [hμ]
  apply (pi_norm_le_iff_of_nonempty _).mpr
  intro i
  fin_cases i
  · change ‖connectionStrongClockPartials (-y 0) (y 1) (y 2) (y 3) 0‖ ≤ 64
    rw [Real.norm_eq_abs]
    exact (connectionStrongClockPartials_bounds hμ hm hu hv hw).1.trans (by norm_num)
  · change ‖μ ^ 2 * connectionWeakClockPartials (-y 0) (y 1) (y 2) (y 3) 0‖ ≤ 64
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg μ)]
    apply (mul_le_mul_of_nonneg_left (connectionWeakClockPartials_bounds hμ hm hu hv hw).1 (sq_nonneg μ)).trans_eq
    field_simp

theorem connectionPhaseColumn_forcing {μ : ℝ} {y : ProjectiveState} (hμ : 4 ≤ μ)
    (hm : |-y 0 - μ| ≤ 1 / 2) (hu : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000)
    (hv : 0 ≤ y 2 ∧ y 2 ≤ 1) (hw : 0 ≤ y 3 ∧ y 3 ≤ 1) (Z : ℝ) :
    ‖Z • connectionPhaseColumn μ y‖ ≤ 64 * |Z| := by
  rw [norm_smul, Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left (connectionPhaseColumn_norm hμ hm hu hv hw) (abs_nonneg Z)).trans_eq (mul_comm _ _)

end BianchiIX
