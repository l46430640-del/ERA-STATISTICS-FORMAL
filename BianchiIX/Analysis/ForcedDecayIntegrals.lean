import BianchiIX.Analysis.CoreIntegrals

noncomputable section

namespace BianchiIX

open Set MeasureTheory

theorem integral_time_exp_decay_le {a b c : ℝ} (hab : a ≤ b) (hc : 0 < c) :
    (∫ t in a..b, (t - a) * Real.exp (-c * (t - a))) ≤ 1 / c ^ 2 := by
  have hd (t : ℝ) : HasDerivAt (fun s => -((s - a) / c + 1 / c ^ 2) * Real.exp (-c * (s - a)))
      ((t - a) * Real.exp (-c * (t - a))) t := by
    convert! ((((hasDerivAt_id t).sub_const a).div_const c).add_const (1 / c ^ 2)).neg.mul
      (((hasDerivAt_id t).sub_const a).const_mul (-c)).exp using 1
    dsimp
    field_simp
    ring
  have hcont : Continuous (fun t => (t - a) * Real.exp (-c * (t - a))) := by fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) (hcont.intervalIntegrable _ _)]
  simp only [sub_self, zero_div, zero_add, mul_zero, Real.exp_zero, mul_one]
  have hnonneg : 0 ≤ ((b - a) / c + 1 / c ^ 2) * Real.exp (-c * (b - a)) :=
    mul_nonneg (add_nonneg (div_nonneg (sub_nonneg.mpr hab) hc.le) (by positivity)) (Real.exp_pos _).le
  linarith only [hnonneg]

theorem integral_le_of_affine_exp_decay {f : ℝ → ℝ} {a b c A B : ℝ}
    (hab : a ≤ b) (hc : 0 < c) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hf : ContinuousOn f (Icc a b))
    (hbound : ∀ t ∈ Icc a b, f t ≤ Real.exp (-c * (t - a)) * (A + B * (t - a))) :
    (∫ t in a..b, f t) ≤ A / c + B / c ^ 2 := by
  have h0 : Continuous (fun t => A * Real.exp (-c * (t - a))) := by fun_prop
  have h1 : Continuous (fun t => B * ((t - a) * Real.exp (-c * (t - a)))) := by fun_prop
  have H := intervalIntegral.integral_mono_on (μ := volume) hab
    (hf.intervalIntegrable_of_Icc hab) ((h0.add h1).intervalIntegrable _ _)
    (fun t ht => (hbound t ht).trans_eq (by dsimp; ring))
  simp only [Pi.add_apply] at H
  rw [intervalIntegral.integral_add (h0.intervalIntegrable _ _) (h1.intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at H
  apply H.trans
  have H' := add_le_add (mul_le_mul_of_nonneg_left (integral_exp_decay_le (a := a) (b := b) hc) hA)
    (mul_le_mul_of_nonneg_left (integral_time_exp_decay_le hab hc) hB)
  convert! H' using 1
  ring

/-- The two explicit integrals in (B.36), with no total-duration factor. -/
theorem core_forced_variation_integrals {x : ℝ → ℝ} {k T z₀ U Q : ℝ}
    (hk : 6 ≤ k) (hT : 0 ≤ T) (hU : 0 ≤ U) (hQ : 0 ≤ Q)
    (hx : ContinuousOn x (Icc 0 T)) (hz₀ : Real.cosh z₀ = k)
    (hbound : ∀ t ∈ Icc 0 T,
      |x t| ≤ Real.exp (-k * t / 4) * (|x 0| + 3 * k * U * Q * t)) :
    (∫ t in 0..T, |x t| / Real.cosh (z₀ + t)) ≤ (12 * |x 0| + 432 * U * Q) / k ^ 2 ∧
      (∫ t in 0..T, |x t|) ≤ (4 * |x 0| + 48 * U * Q) / k := by
  have hk0 : 0 < k := by linarith only [hk]
  have hc : 0 < k / 4 := by positivity
  have hrate : k / 12 ≤ k / 4 - 1 := by linarith only [hk]
  have hrate0 : 0 < k / 4 - 1 := lt_of_lt_of_le (by positivity) hrate
  have hdecay (t : ℝ) (ht : t ∈ Icc 0 T) :
      |x t| ≤ Real.exp (-(k / 4) * (t - 0)) * (|x 0| + (3 * k * U * Q) * (t - 0)) := by
    convert! hbound t ht using 1
    congr 2 <;> ring
  constructor
  · have hweighted : ContinuousOn (fun t => |x t| / Real.cosh (z₀ + t)) (Icc 0 T) :=
      hx.abs.div (by fun_prop) (fun t _ => ne_of_gt (Real.cosh_pos _))
    have hpoint (t : ℝ) (ht : t ∈ Icc 0 T) :
        |x t| / Real.cosh (z₀ + t) ≤
          Real.exp (-(k / 4 - 1) * (t - 0)) * (|x 0| / k + (3 * U * Q) * (t - 0)) := by
      have hs := sech_le_exp (a := z₀) (b := z₀ + t) (by linarith only [ht.1])
      rw [hz₀, add_sub_cancel_left] at hs
      have H := mul_le_mul hs (hbound t ht) (abs_nonneg _) (by positivity : 0 ≤ (1 / k) * Real.exp t)
      calc
        _ = (1 / Real.cosh (z₀ + t)) * |x t| := by ring
        _ ≤ (1 / k * Real.exp t) * (Real.exp (-k * t / 4) * (|x 0| + 3 * k * U * Q * t)) := H
        _ = (Real.exp t * Real.exp (-k * t / 4)) * (|x 0| / k + 3 * U * Q * t) := by field_simp
        _ = _ := by
          rw [← Real.exp_add]
          congr 2 <;> ring
    have H := integral_le_of_affine_exp_decay hT hrate0 (div_nonneg (abs_nonneg _) hk0.le)
      (by positivity : 0 ≤ 3 * U * Q) hweighted hpoint
    have hrate2 := (sq_le_sq₀ (by positivity : 0 ≤ k / 12) hrate0.le).mpr hrate
    apply H.trans
    calc
      _ ≤ (|x 0| / k) / (k / 12) + (3 * U * Q) / (k / 12) ^ 2 := add_le_add
        (div_le_div_of_nonneg_left (by positivity) (by positivity) hrate)
        (div_le_div_of_nonneg_left (by positivity) (by positivity) hrate2)
      _ = _ := by field_simp; ring
  · have H := integral_le_of_affine_exp_decay hT hc (abs_nonneg (x 0))
      (by positivity : 0 ≤ 3 * k * U * Q) hx.abs hdecay
    convert! H using 1
    field_simp
    ring

end BianchiIX
