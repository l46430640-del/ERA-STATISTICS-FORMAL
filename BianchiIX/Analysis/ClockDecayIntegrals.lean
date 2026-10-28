import BianchiIX.Analysis.CoreIntegrals
import BianchiIX.Analysis.DampedForcing

noncomputable section

namespace BianchiIX

open Set MeasureTheory

theorem integral_clock_exp_decay {z z' : ℝ → ℝ} {a b c : ℝ}
    (hab : a ≤ b) (hc : 0 < c)
    (hz : ∀ t ∈ Icc a b, HasDerivAt z (z' t) t)
    (hzc : ContinuousOn z' (Icc a b)) :
    (∫ t in a..b, z' t * Real.exp (-c * (z t - z a))) =
      (1 - Real.exp (-c * (z b - z a))) / c := by
  have hd (t : ℝ) (ht : t ∈ Icc a b) :
      HasDerivAt (fun s => -Real.exp (-c * (z s - z a)) / c)
        (z' t * Real.exp (-c * (z t - z a))) t := by
    convert! (((hz t ht).sub_const (z a)).const_mul (-c)).exp.neg.div_const c using 1
    field_simp
  have hint : IntervalIntegrable (fun t => z' t * Real.exp (-c * (z t - z a))) volume a b :=
    (hzc.mul (Real.continuous_exp.comp_continuousOn
      (((HasDerivAt.continuousOn hz).sub continuousOn_const).const_mul (-c)))).intervalIntegrable_of_Icc hab
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => hd t (uIcc_of_le hab ▸ ht)) hint]
  simp only [sub_self, mul_zero, Real.exp_zero]
  ring

theorem integral_clock_exp_decay_le {z z' : ℝ → ℝ} {a b c : ℝ}
    (hab : a ≤ b) (hc : 0 < c)
    (hz : ∀ t ∈ Icc a b, HasDerivAt z (z' t) t)
    (hzc : ContinuousOn z' (Icc a b)) :
    (∫ t in a..b, z' t * Real.exp (-c * (z t - z a))) ≤ 1 / c := by
  rw [integral_clock_exp_decay hab hc hz hzc]
  exact (div_le_div_iff_of_pos_right hc).mpr (by linarith [Real.exp_pos (-c * (z b - z a))])

theorem abs_le_exp_of_clock_damping {f d z z' : ℝ → ℝ} {a b c : ℝ}
    (hf : ∀ t ∈ Icc a b, HasDerivAt f (z' t * (d t * f t)) t)
    (hz : ∀ t ∈ Icc a b, HasDerivAt z (z' t) t)
    (hzpos : ∀ t ∈ Icc a b, 0 ≤ z' t)
    (hd : ∀ t ∈ Icc a b, d t ≤ -c) :
    ∀ t ∈ Icc a b, |f t| ≤ |f a| * Real.exp (-c * (z t - z a)) := by
  have H := abs_le_affine_exp_of_clock_damping (g := fun _ => 0) (B := 0)
    (by simpa only [add_zero] using hf) hz hzpos hd (by simp)
  simpa only [zero_mul, mul_zero, add_zero, mul_comm] using H

end BianchiIX
