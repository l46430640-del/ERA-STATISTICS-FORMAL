import BianchiIX.Dynamics.StableClockResidualUniform
import BianchiIX.Analysis.ImproperIntegralDerivative

noncomputable section

namespace BianchiIX

open Set MeasureTheory

local instance stableClockTailNormedAddCommGroup : NormedAddCommGroup (StableState →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance stableClockTailNormedSpace : NormedSpace ℝ (StableState →L[ℝ] ℝ) := inferInstance

def stableClockTailIntegral (c T : ℝ) (y : StableState) : ℝ :=
  ∫ s in Ioi T, stableClockResidualRate c s y

theorem stableClockTailIntegral_derivatives {c T : ℝ} {y : StableState}
    (hc : 2 ≤ c) (hy : y ∈ stableParameterDomain c) (hT : 0 ≤ T) :
    IntegrableOn (fun s => fderiv ℝ (stableClockResidualRate c s) y) (Ioi T) ∧
      IntegrableOn (fun s => fderiv ℝ (fderiv ℝ (stableClockResidualRate c s)) y) (Ioi T) ∧
      fderiv ℝ (stableClockTailIntegral c T) y =
        (∫ s in Ioi T, fderiv ℝ (stableClockResidualRate c s) y) ∧
      fderiv ℝ (fderiv ℝ (stableClockTailIntegral c T)) y =
        ∫ s in Ioi T, fderiv ℝ (fderiv ℝ (stableClockResidualRate c s)) y := by
  obtain ⟨C, hC, HC⟩ := exists_stableClockResidualRate_uniform_bounds
  obtain ⟨A, hA, HA⟩ := exists_stableClockResidual_derivative_integral_tails
  let B := fun s => C / (c + 1) ^ 2 * Real.exp (-(c + 1) / 16 * s)
  have hB : IntegrableOn B (Ioi T) :=
    (integrableOn_exp_mul_Ioi (by linarith : -(c + 1) / 16 < 0) T).const_mul _
  exact fderiv2_integral_Ioi_of_contDiffAt
    (f := fun p : ℝ × StableState => stableClockResidualRate c p.1 p.2)
    (isOpen_stableParameterDomain c) hy
    (fun z hz s hs => contDiffAt_stableClockResidualRate_joint_two hc hz (le_trans hT hs.le))
    (fun z hz => (HA c T z hc hz hT).1.1) hB
    (fun z hz s hs => (HC c s z hc hz (le_trans hT hs.le)).2.1)
    (fun z hz s hs => (HC c s z hc hz (le_trans hT hs.le)).2.2)

theorem stableClockTailIntegral_fderiv_apply {c T : ℝ} {y : StableState}
    (hc : 2 ≤ c) (hy : y ∈ stableParameterDomain c) (hT : 0 ≤ T) (v : StableState) :
    fderiv ℝ (stableClockTailIntegral c T) y v =
      ∫ s in Ioi T, fderiv ℝ (stableClockResidualRate c s) y v := by
  have H := stableClockTailIntegral_derivatives hc hy hT
  rw [H.2.2.1]
  exact ContinuousLinearMap.integral_apply H.1 v

theorem stableClockTailIntegral_fderiv2_apply {c T : ℝ} {y : StableState}
    (hc : 2 ≤ c) (hy : y ∈ stableParameterDomain c) (hT : 0 ≤ T) (v w : StableState) :
    fderiv ℝ (fderiv ℝ (stableClockTailIntegral c T)) y v w =
      ∫ s in Ioi T, fderiv ℝ (fderiv ℝ (stableClockResidualRate c s)) y v w := by
  have H := stableClockTailIntegral_derivatives hc hy hT
  rw [H.2.2.2, ContinuousLinearMap.integral_apply H.2.1 v]
  exact ContinuousLinearMap.integral_apply
    ((ContinuousLinearMap.apply ℝ (StableState →L[ℝ] ℝ) v).integrable_comp H.2.1) w

end BianchiIX
