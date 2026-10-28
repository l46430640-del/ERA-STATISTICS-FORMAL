import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Inv

noncomputable section

namespace BianchiIX

open Set MeasureTheory

theorem integral_le_of_dissipation {f f' g : ℝ → ℝ} {a b c : ℝ}
    (hab : a ≤ b) (hc : 0 < c)
    (hf : ∀ t ∈ Icc a b, HasDerivAt f (f' t) t)
    (hg : ContinuousOn g (Icc a b))
    (hbound : ∀ t ∈ Icc a b, f' t ≤ -c * g t) (hfb : 0 ≤ f b) :
    (∫ t in a..b, g t) ≤ f a / c := by
  have hderiv (t : ℝ) (ht : t ∈ Icc a b) := (hf t ht).neg.div_const c
  have H := intervalIntegral.integral_le_sub_of_hasDeriv_right_of_le hab
    (fun t ht => (hderiv t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hderiv t (Ioo_subset_Icc_self ht)).hasDerivWithinAt)
    hg.integrableOn_Icc (fun t ht => ?_)
  · apply H.trans
    have hbc : 0 ≤ f b / c := div_nonneg hfb hc.le
    simp only [Pi.neg_apply, neg_div]
    linarith only [hbc]
  · apply (le_div_iff₀ hc).mpr
    nlinarith only [hbound t (Ioo_subset_Icc_self ht)]

end BianchiIX
