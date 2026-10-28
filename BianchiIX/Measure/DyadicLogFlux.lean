import BianchiIX.Measure.DyadicFlux

noncomputable section

namespace BianchiIX

open MeasureTheory
open scoped ENNReal

theorem hasSum_dyadic_log_abs {d : ℝ} (hd : 0 < d) (hd1 : d ≤ 1) :
    HasSum (fun j => dyadicScale d j * |Real.log (dyadicScale d j)|)
      (d * (|Real.log d| + 2 * Real.log 2)) := by
  have H := (hasSum_dyadic_weights.mul_left |Real.log d|).add
    (hasSum_dyadic_first_moment.mul_left (Real.log 2))
  convert! H.mul_left d using 1
  · ext j
    rw [abs_of_nonpos (Real.log_nonpos (dyadicScale_pos hd j).le ((dyadicScale_le hd.le j).trans hd1)),
      log_dyadicScale hd, abs_of_nonpos (Real.log_nonpos hd.le hd1)]
    dsimp only [dyadicScale]
    ring
  · ring

theorem dyadic_log_flux_sum {d C : ℝ} (hd : 0 < d) (hd1 : d ≤ 1) (hC : 0 ≤ C) :
    (∑' j, ENNReal.ofReal (C * (dyadicScale d j * |Real.log (dyadicScale d j)|))) =
      ENNReal.ofReal (C * d * (|Real.log d| + 2 * Real.log 2)) := by
  rw [← ENNReal.ofReal_tsum_of_nonneg
    (fun j => mul_nonneg hC (mul_nonneg (dyadicScale_pos hd j).le (abs_nonneg _)))
    ((hasSum_dyadic_log_abs hd hd1).summable.mul_left C), tsum_mul_left,
    (hasSum_dyadic_log_abs hd hd1).tsum_eq]
  congr 1
  ring

end BianchiIX
