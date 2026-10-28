import BianchiIX.Dynamics.CoreContraction

noncomputable section

namespace BianchiIX

open Set

/-- The two signs of the same scalar comparison give a two-sided multiplicative bound. -/
theorem scalar_clock_comparison {f f' z z' : ℝ → ℝ} {a b : ℝ}
    (hf : ∀ t ∈ Icc a b, HasDerivAt f (f' t) t)
    (hz : ∀ t ∈ Icc a b, HasDerivAt z (z' t) t)
    (hb : ∀ t ∈ Icc a b, |f' t| ≤ z' t * f t) :
    ∀ t ∈ Icc a b,
      f a * Real.exp (-(z t - z a)) ≤ f t ∧ f t ≤ f a * Real.exp (z t - z a) := by
  intro t ht
  have ha : a ∈ Icc a b := ⟨le_rfl, ht.1.trans ht.2⟩
  have HU := le_exp_of_clock_deriv_le (convex_Icc a b) hf hz (c := 1)
    (fun s hs => by simpa only [one_mul] using (le_abs_self _).trans (hb s hs)) ha ht ht.1
  have HL := le_exp_of_clock_deriv_le (convex_Icc a b) (fun s hs => (hf s hs).neg) hz (c := -1)
    (fun s hs => by
      change -f' s ≤ -1 * z' s * (-f s)
      nlinarith only [neg_le_abs (f' s), hb s hs]) ha ht ht.1
  simp only [one_mul] at HU
  simp only [Pi.neg_apply, neg_one_mul] at HL
  exact ⟨by linarith only [HL], HU⟩

/-- An explicit primitive bounds the accumulated additive error without regularity of the derivative. -/
theorem abs_sub_le_of_deriv_primitive {f f' z z' : ℝ → ℝ} {a b : ℝ}
    (hf : ∀ t ∈ Icc a b, HasDerivAt f (f' t) t)
    (hz : ∀ t ∈ Icc a b, HasDerivAt z (z' t) t)
    (hb : ∀ t ∈ Icc a b, |f' t| ≤ z' t) :
    ∀ t ∈ Icc a b, |f t - f a| ≤ z t - z a := by
  intro t ht
  have ha : a ∈ Icc a b := ⟨le_rfl, ht.1.trans ht.2⟩
  have HU := le_exp_of_linear_deriv_le (convex_Icc a b) (fun s hs => (hf s hs).sub (hz s hs)) (c := 0)
    (fun s hs => by nlinarith only [le_abs_self (f' s), hb s hs]) ha ht ht.1
  have HL := le_exp_of_linear_deriv_le (convex_Icc a b) (fun s hs => (hf s hs).neg.sub (hz s hs)) (c := 0)
    (fun s hs => by nlinarith only [neg_le_abs (f' s), hb s hs]) ha ht ht.1
  simp only [zero_mul, Real.exp_zero, mul_one, Pi.sub_apply, Pi.neg_apply] at HU HL
  exact abs_le.mpr ⟨by linarith only [HL], by linarith only [HU]⟩

end BianchiIX
