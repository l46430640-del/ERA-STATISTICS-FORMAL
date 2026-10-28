import BianchiIX.Analysis.ClockEnvelope
import Mathlib.Analysis.SpecialFunctions.Arcosh

noncomputable section

namespace BianchiIX

open Set MeasureTheory

/-- The unweighted integral depends only on angle differences, not on an entrance section. -/
theorem partial_core_clock_variation_integral {x z rate : ℝ → ℝ} {k a b U Q : ℝ}
    (hk : 6 ≤ k) (hab : a ≤ b) (hU : 0 ≤ U) (hQ : 0 ≤ Q)
    (hx : ContinuousOn x (Icc a b)) (hz : ∀ t ∈ Icc a b, HasDerivAt z (rate t) t)
    (hrate : ContinuousOn rate (Icc a b)) (hpos : ∀ t ∈ Icc a b, 0 ≤ rate t)
    (hbound : ∀ t ∈ Icc a b, |x t| ≤ Real.exp (-k * (z t - z a) / 4) *
      (|x a| + 3 * k * U * Q * (z t - z a))) :
    (∫ t in a..b, |x t| * rate t) ≤ (4 * |x a| + 48 * U * Q) / k := by
  let Z := fun t => z t - z a + Real.arcosh k
  have hZ (t : ℝ) (ht : t ∈ Icc a b) : HasDerivAt Z (rate t) t :=
    ((hz t ht).sub_const (z a)).add_const (Real.arcosh k)
  have hentry : Real.cosh (Z a) = k := by
    simp only [Z, sub_self, zero_add]
    exact Real.cosh_arcosh (by linarith only [hk])
  have hdiff (t : ℝ) : Z t - Z a = z t - z a := by dsimp [Z]; ring
  exact (core_clock_forced_variation_integrals hk hab hU hQ hx hZ hrate hpos hentry
    (fun t ht => by rw [hdiff]; exact hbound t ht)).2

end BianchiIX
