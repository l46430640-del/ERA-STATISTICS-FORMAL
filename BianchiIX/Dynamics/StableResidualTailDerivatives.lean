import BianchiIX.Dynamics.StableResidualUniformBounds
import BianchiIX.Analysis.ImproperIntegralDerivative

noncomputable section

namespace BianchiIX

open Set MeasureTheory

local instance : NormedAddCommGroup (StableState →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (StableState →L[ℝ] ℝ) := inferInstance

def stableResidualTailIntegral (K T : ℝ) (y : StableState) : ℝ :=
  ∫ s in Ioi T, stableRescaledResidualRate K s y

theorem stableResidualTailIntegral_derivatives {c T : ℝ} {y : StableState}
    (hc : 2 ≤ c) (hy : y ∈ stableParameterDomain c) (hT : 0 ≤ T) :
    IntegrableOn (fun s => fderiv ℝ (stableRescaledResidualRate (c + 1) s) y) (Ioi T) ∧
      IntegrableOn (fun s => fderiv ℝ (fderiv ℝ (stableRescaledResidualRate (c + 1) s)) y) (Ioi T) ∧
      fderiv ℝ (stableResidualTailIntegral (c + 1) T) y =
        (∫ s in Ioi T, fderiv ℝ (stableRescaledResidualRate (c + 1) s) y) ∧
      fderiv ℝ (fderiv ℝ (stableResidualTailIntegral (c + 1) T)) y =
        ∫ s in Ioi T, fderiv ℝ (fderiv ℝ (stableRescaledResidualRate (c + 1) s)) y := by
  obtain ⟨C, hC, HC⟩ := exists_stableRescaledResidualRate_uniform_bounds
  obtain ⟨A, hA, HA⟩ := exists_stableResidual_derivative_integral_tails
  have hK : 0 < c + 1 := by linarith
  let B := fun s => C / (c + 1) ^ 2 * Real.exp (-(c + 1) / 16 * s)
  have hB : IntegrableOn B (Ioi T) :=
    (integrableOn_exp_mul_Ioi (by linarith : -(c + 1) / 16 < 0) T).const_mul _
  exact fderiv2_integral_Ioi_of_contDiffAt
    (f := fun p : ℝ × StableState => stableRescaledResidualRate (c + 1) p.1 p.2)
    (isOpen_stableParameterDomain c) hy
    (fun z hz s hs => contDiffAt_stableRescaledResidualRate_joint_two hc hz.1.le hz.2.1.le hz.2.2.le (le_trans hT hs.le))
    (fun z hz => (HA c T z hc hz.1 hz.2.1 hz.2.2 hT).1.1) hB
    (fun z hz s hs => (HC c s z hc hz (le_trans hT hs.le)).2.1)
    (fun z hz s hs => (HC c s z hc hz (le_trans hT hs.le)).2.2)

theorem stableResidualTailIntegral_fderiv_apply {c T : ℝ} {y : StableState}
    (hc : 2 ≤ c) (hy : y ∈ stableParameterDomain c) (hT : 0 ≤ T) (v : StableState) :
    fderiv ℝ (stableResidualTailIntegral (c + 1) T) y v =
      ∫ s in Ioi T, fderiv ℝ (stableRescaledResidualRate (c + 1) s) y v := by
  have H := stableResidualTailIntegral_derivatives hc hy hT
  rw [H.2.2.1]
  exact ContinuousLinearMap.integral_apply H.1 v

theorem stableResidualTailIntegral_fderiv2_apply {c T : ℝ} {y : StableState}
    (hc : 2 ≤ c) (hy : y ∈ stableParameterDomain c) (hT : 0 ≤ T) (v w : StableState) :
    fderiv ℝ (fderiv ℝ (stableResidualTailIntegral (c + 1) T)) y v w =
      ∫ s in Ioi T, fderiv ℝ (fderiv ℝ (stableRescaledResidualRate (c + 1) s)) y v w := by
  have H := stableResidualTailIntegral_derivatives hc hy hT
  rw [H.2.2.2, ContinuousLinearMap.integral_apply H.2.1 v]
  exact ContinuousLinearMap.integral_apply
    ((ContinuousLinearMap.apply ℝ (StableState →L[ℝ] ℝ) v).integrable_comp H.2.1) w

end BianchiIX
