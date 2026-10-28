import BianchiIX.Analysis.ClockEnvelope

noncomputable section

namespace BianchiIX

open Set MeasureTheory

theorem integral_clock_le_of_cosh_sq {f z rate : ℝ → ℝ} {a b B K : ℝ}
    (hab : a ≤ b) (hz : ∀ t ∈ Icc a b, HasDerivAt z (rate t) t)
    (hrate : ContinuousOn rate (Icc a b)) (hpos : ∀ t ∈ Icc a b, 0 ≤ rate t)
    (hB : 0 ≤ B) (hf : ContinuousOn f (Icc a b))
    (hbound : ∀ t ∈ Icc a b, f t ≤ B * Real.cosh (z t) ^ 2)
    (ha : Real.cosh (z a) ≤ K) (hb : Real.cosh (z b) ≤ K) :
    (∫ t in a..b, f t * rate t) ≤ 2 * B * K ^ 2 := by
  have hzc : ContinuousOn z (Icc a b) := fun t ht => (hz t ht).continuousAt.continuousWithinAt
  have hmono : MonotoneOn z (Icc a b) := monotoneOn_of_deriv_nonneg (convex_Icc a b) hzc
    (fun t ht => (hz t (interior_subset ht)).differentiableAt.differentiableWithinAt)
    (fun t ht => by rw [(hz t (interior_subset ht)).deriv]; exact hpos t (interior_subset ht))
  have hzab := hmono ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab
  have hG : Continuous (fun s => B * Real.cosh s ^ 2) := by fun_prop
  exact (integral_clock_le_envelope hab hz hrate hpos hf hG hbound).trans
    (integral_le_of_cosh_sq hzab hB hG.continuousOn (fun _ _ => le_rfl) ha hb)

theorem integral_clock_le_of_exp_decay {f z rate : ℝ → ℝ} {a b c B : ℝ}
    (hab : a ≤ b) (hz : ∀ t ∈ Icc a b, HasDerivAt z (rate t) t)
    (hrate : ContinuousOn rate (Icc a b)) (hpos : ∀ t ∈ Icc a b, 0 ≤ rate t)
    (hc : 0 < c) (hB : 0 ≤ B) (hf : ContinuousOn f (Icc a b))
    (hbound : ∀ t ∈ Icc a b, f t ≤ B * Real.exp (-c * (z t - z a))) :
    (∫ t in a..b, f t * rate t) ≤ B / c := by
  have hG : Continuous (fun s => B * Real.exp (-c * (s - z a))) := by fun_prop
  have H := integral_clock_le_envelope hab hz hrate hpos hf hG hbound
  rw [intervalIntegral.integral_const_mul] at H
  exact H.trans ((mul_le_mul_of_nonneg_left (integral_exp_decay_le hc) hB).trans_eq (by ring))

end BianchiIX
