import BianchiIX.Dynamics.StableResidualClockBounds
import BianchiIX.Algebra.StableResidualDerivativeBounds
import BianchiIX.Analysis.SecondDerivativeBounds

noncomputable section

namespace BianchiIX

def stableCenterWeakProjection : StableState →L[ℝ] (Fin 2 → ℝ) :=
  ContinuousLinearMap.pi ![ContinuousLinearMap.proj 0, ContinuousLinearMap.proj 2]

theorem stableCenterWeakProjection_apply (y : StableState) :
    stableCenterWeakProjection y = ![y 0, y 2] := by ext i; fin_cases i <;> rfl

theorem stableCenterWeakProjection_norm : ‖stableCenterWeakProjection‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro y
  rw [one_mul, stableCenterWeakProjection_apply]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg y)).mpr
  intro i; fin_cases i
  · exact norm_le_pi_norm y 0
  · exact norm_le_pi_norm y 2

def stableScaledResidualCoefficient (K : ℝ) (i : Fin 4) (y : StableState) : ℝ :=
  stableResidualClock K y * stableResidualCoefficient i (stableCenterWeakProjection y)

theorem exists_stableScaledResidualCoefficient_bounds :
    ∃ C > (0 : ℝ), ∀ (c : ℝ) (y : StableState), 2 ≤ c → |y 0 - c| ≤ 1 / 10 →
      |y 1| ≤ 1 / 100 → |y 2| ≤ 1 / 100 → ∀ i : Fin 4,
      ContDiffAt ℝ 2 (stableScaledResidualCoefficient (c + 1) i) y ∧
        |stableScaledResidualCoefficient (c + 1) i y| ≤ C / (c + 1) ^ 2 ∧
        ‖fderiv ℝ (stableScaledResidualCoefficient (c + 1) i) y‖ ≤ C / (c + 1) ^ 2 ∧
        ‖fderiv ℝ (fderiv ℝ (stableScaledResidualCoefficient (c + 1) i)) y‖ ≤ C / (c + 1) ^ 2 := by
  obtain ⟨C, hC, HC⟩ := exists_stableResidualCoefficient_band_derivative_bounds
  refine ⟨6000 * C, by positivity, ?_⟩
  intro c y hc hm hu hw i
  have hK : 0 < c + 1 := by linarith
  have hmw : |stableCenterWeakProjection y 0 - c| ≤ 1 / 10 := hm
  have hww : |stableCenterWeakProjection y 1| ≤ 1 := by change |y 2| ≤ 1; linarith
  obtain ⟨hg, hg0, hg1, hg2⟩ := HC c (stableCenterWeakProjection y) hc hmw hww i
  have hpre := clm_precomp_second_derivative_bounds stableCenterWeakProjection stableCenterWeakProjection_norm
    (by positivity : 0 ≤ C / (c + 1)) hg hg1 hg2
  have hcomp : ContDiffAt ℝ 2 (stableResidualCoefficient i ∘ stableCenterWeakProjection) y :=
    hg.comp y stableCenterWeakProjection.contDiff.contDiffAt
  obtain ⟨hq0, hq1, hq2⟩ := stableResidualClock_derivative_bounds hc hm hu hw
  have hreg : ContDiffAt ℝ 2 (stableResidualClock (c + 1)) y :=
    (contDiff_stableResidualClock 2 (c + 1)).contDiffAt
  obtain ⟨H0, H1, H2⟩ := product_second_derivative_bounds hreg hcomp
    (by positivity : 0 ≤ 1500 / (c + 1)) (by positivity : 0 ≤ C / (c + 1))
    hq0 hq1 hq2 hg0 hpre.1 hpre.2
  have hsame : stableScaledResidualCoefficient (c + 1) i =
      (fun z => stableResidualClock (c + 1) z * (stableResidualCoefficient i ∘ stableCenterWeakProjection) z) := rfl
  rw [hsame]
  refine ⟨hreg.mul hcomp, ?_⟩
  have hnonneg : 0 ≤ C / (c + 1) ^ 2 := by positivity
  simp only [div_eq_mul_inv, ← inv_pow] at H0 H1 H2 hnonneg ⊢
  exact ⟨by nlinarith only [H0, hnonneg], by nlinarith only [H1, hnonneg], by nlinarith only [H2]⟩

end BianchiIX
