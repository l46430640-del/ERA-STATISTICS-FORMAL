import BianchiIX.Analysis.CoreIntegrals

noncomputable section

namespace BianchiIX

open Set MeasureTheory

/-- Keep the two decaying clock weights separate from the constant feedback. -/
theorem integral_exit_tail_envelope {T A B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C) :
    (∫ s in (0 : ℝ)..T, A + B * Real.exp (-s) + C * Real.exp (-2 * s)) ≤ A * T + B + C / 2 := by
  have h0 : IntervalIntegrable (fun _ : ℝ => A) volume 0 T := intervalIntegrable_const
  have h1 : IntervalIntegrable (fun s => B * Real.exp (-s)) volume 0 T :=
    (by fun_prop : Continuous (fun s : ℝ => B * Real.exp (-s))).intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun s => C * Real.exp (-2 * s)) volume 0 T :=
    (by fun_prop : Continuous (fun s : ℝ => C * Real.exp (-2 * s))).intervalIntegrable _ _
  rw [intervalIntegral.integral_add (h0.add h1) h2, intervalIntegral.integral_add h0 h1,
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have H1 := integral_exp_decay_le (a := 0) (b := T) (by norm_num : (0 : ℝ) < 1)
  have H2 := integral_exp_decay_le (a := 0) (b := T) (by norm_num : (0 : ℝ) < 2)
  simp only [sub_zero, neg_mul, one_mul, one_div_one] at H1 H2
  simp only [sub_zero, smul_eq_mul, neg_mul]
  nlinarith only [mul_le_mul_of_nonneg_left H1 hB, mul_le_mul_of_nonneg_left H2 hC]

theorem integral_abs_le_exit_tail_envelope {f : ℝ → ℝ} {T A B C : ℝ} (hT : 0 ≤ T)
    (hB : 0 ≤ B) (hC : 0 ≤ C) (hf : ContinuousOn f (Icc 0 T))
    (hbound : ∀ s ∈ Icc 0 T, |f s| ≤ A + B * Real.exp (-s) + C * Real.exp (-2 * s)) :
    (∫ s in (0 : ℝ)..T, |f s|) ≤ A * T + B + C / 2 := by
  have hc : Continuous (fun s : ℝ => A + B * Real.exp (-s) + C * Real.exp (-2 * s)) := by fun_prop
  exact (intervalIntegral.integral_mono_on hT (hf.abs.intervalIntegrable_of_Icc hT)
    (hc.intervalIntegrable _ _) hbound).trans (integral_exit_tail_envelope hB hC)

end BianchiIX
