import BianchiIX.Dynamics.StableResidualRateRegularity
import BianchiIX.Analysis.ExponentialTailIntegral

noncomputable section

namespace BianchiIX

open Set MeasureTheory

theorem exists_stableResidual_derivative_integral_tails :
    ∃ C > (0 : ℝ), ∀ (c T : ℝ) (y : StableState), 2 ≤ c → |y 0 - c| < 1 / 40 →
      |y 1| < 1 / 200 → |y 2| < 1 / 200 → 0 ≤ T →
      let b := |y 1| + |y 2|
      let q := Real.exp (-(c + 1) / 16 * T)
      (IntegrableOn (fun s => stableRescaledResidualRate (c + 1) s y) (Ioi T) ∧
        |∫ s in Ioi T, stableRescaledResidualRate (c + 1) s y| ≤
          C / (c + 1) ^ 3 * |y 1| * b ^ 3 * q) ∧
      (∀ v, IntegrableOn (fun s => fderiv ℝ (stableRescaledResidualRate (c + 1) s) y v) (Ioi T) ∧
        |∫ s in Ioi T, fderiv ℝ (stableRescaledResidualRate (c + 1) s) y v| ≤
          C / (c + 1) ^ 3 * b ^ 3 * stableFirstInputWeight b v * q) ∧
      (∀ v w, IntegrableOn (fun s => fderiv ℝ (fderiv ℝ (stableRescaledResidualRate (c + 1) s)) y v w) (Ioi T) ∧
        |∫ s in Ioi T, fderiv ℝ (fderiv ℝ (stableRescaledResidualRate (c + 1) s)) y v w| ≤
          C / (c + 1) ^ 3 * b ^ 2 * stableFirstInputWeight b v * stableFirstInputWeight b w * q) := by
  obtain ⟨C, hC, HC⟩ := exists_stableRescaledResidualRate_weighted_decay
  refine ⟨16 * C, by positivity, ?_⟩
  intro c T y hc hm hu hw hT
  dsimp only
  have hK : 0 < c + 1 := by linarith
  obtain ⟨hcont0, hcont1, hcont2⟩ := continuousOn_stableRescaledResidualRate_derivatives hc hm.le hu.le hw.le
  refine ⟨?_, ?_, ?_⟩
  · have hbound (s : ℝ) (hs : 0 ≤ s) :
        |stableRescaledResidualRate (c + 1) s y| ≤
          (C * |y 1| * (|y 1| + |y 2|) ^ 3) / (c + 1) ^ 2 * Real.exp (-(c + 1) / 16 * s) := by
      convert! (HC c s y hc hm hu hw hs).2.1 using 1
      ring
    obtain ⟨hi, H⟩ := integrableOn_integral_tail_of_exp_bound hK hT hcont0 hbound
    refine ⟨hi, ?_⟩
    convert! H using 1
    ring
  · intro v
    have hbound (s : ℝ) (hs : 0 ≤ s) :
        |fderiv ℝ (stableRescaledResidualRate (c + 1) s) y v| ≤
          (C * (|y 1| + |y 2|) ^ 3 * stableFirstInputWeight (|y 1| + |y 2|) v) / (c + 1) ^ 2 *
            Real.exp (-(c + 1) / 16 * s) := by
      convert! (HC c s y hc hm hu hw hs).2.2.1 v using 1
      ring
    obtain ⟨hi, H⟩ := integrableOn_integral_tail_of_exp_bound hK hT (hcont1 v) hbound
    refine ⟨hi, ?_⟩
    convert! H using 1
    ring
  · intro v w
    have hbound (s : ℝ) (hs : 0 ≤ s) :
        |fderiv ℝ (fderiv ℝ (stableRescaledResidualRate (c + 1) s)) y v w| ≤
          (C * (|y 1| + |y 2|) ^ 2 * stableFirstInputWeight (|y 1| + |y 2|) v *
            stableFirstInputWeight (|y 1| + |y 2|) w) / (c + 1) ^ 2 * Real.exp (-(c + 1) / 16 * s) := by
      convert! (HC c s y hc hm hu hw hs).2.2.2 v w using 1
      ring
    obtain ⟨hi, H⟩ := integrableOn_integral_tail_of_exp_bound hK hT (hcont2 v w) hbound
    refine ⟨hi, ?_⟩
    convert! H using 1
    ring

end BianchiIX
