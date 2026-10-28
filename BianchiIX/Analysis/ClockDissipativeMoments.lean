import BianchiIX.Analysis.DissipativeMoments
import Mathlib.Analysis.Calculus.Deriv.MeanValue

noncomputable section

namespace BianchiIX

open Set MeasureTheory

/-- A dissipative observable controls both clock moments without an exponential envelope. -/
theorem integral_clock_moments_le_of_dissipation {f f' z q : ℝ → ℝ} {a b c : ℝ}
    (hab : a ≤ b) (hc : 0 < c)
    (hf : ∀ t ∈ Icc a b, HasDerivAt f (f' t) t)
    (hz : ∀ t ∈ Icc a b, HasDerivAt z (q t) t)
    (hqc : ContinuousOn q (Icc a b)) (hq : ∀ t ∈ Icc a b, 0 ≤ q t)
    (hdecay : ∀ t ∈ Icc a b, f' t ≤ -c * (f t * q t)) (hfb : 0 ≤ f b) :
    (∫ t in a..b, f t * q t) ≤ f a / c ∧
      (∫ t in a..b, (z t - z a) * f t * q t) ≤ f a / c ^ 2 := by
  have hfc := HasDerivAt.continuousOn hf
  have hzc := HasDerivAt.continuousOn hz
  have hmono : MonotoneOn z (Icc a b) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a b) hzc
      (fun t ht => (hz t (interior_subset ht)).hasDerivWithinAt)
      (fun t ht => hq t (interior_subset ht))
  have hnonneg (t : ℝ) (ht : t ∈ Icc a b) : 0 ≤ z t - z a :=
    sub_nonneg.mpr (hmono ⟨le_rfl, hab⟩ ht ht.1)
  refine ⟨integral_le_of_dissipation hab hc hf (hfc.mul hqc) hdecay hfb, ?_⟩
  have hd (t : ℝ) (ht : t ∈ Icc a b) :
      HasDerivAt (fun s => (1 + c * (z s - z a)) * f s)
        (c * q t * f t + (1 + c * (z t - z a)) * f' t) t := by
    exact ((((hz t ht).sub_const (z a)).const_mul c).const_add 1).mul (hf t ht)
  have H := integral_le_of_dissipation (g := fun t => (z t - z a) * f t * q t)
    hab (sq_pos_of_pos hc) hd (((hzc.sub continuousOn_const).mul hfc).mul hqc) (fun t ht => ?_) ?_
  · simpa only [sub_self, mul_zero, add_zero, one_mul] using H
  · have hfactor : 0 ≤ 1 + c * (z t - z a) := by positivity [hnonneg t ht]
    calc
      _ ≤ c * q t * f t + (1 + c * (z t - z a)) * (-c * (f t * q t)) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left (hdecay t ht) hfactor)
      _ = _ := by ring
  · exact mul_nonneg (by positivity [hnonneg b ⟨hab, le_rfl⟩]) hfb

end BianchiIX
