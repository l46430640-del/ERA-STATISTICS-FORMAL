import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Exact normalized vacuum Bianchi IX equations. -/

namespace BianchiIX

noncomputable section

def curvature (a b c : ℝ) : ℝ :=
  a ^ 2 + b ^ 2 + c ^ 2 - 2 * (a * b + b * c + c * a)

def shearSq (p s : ℝ) : ℝ := p ^ 2 + s ^ 2

def constraint (p s a b c : ℝ) : ℝ := shearSq p s + curvature a b c

def shearPlus (p a b c : ℝ) : ℝ :=
  curvature a b c * p - 2 * a ^ 2 + b ^ 2 + c ^ 2 + a * b - 2 * b * c + a * c

def shearMinus (s a b c : ℝ) : ℝ :=
  curvature a b c * s + Real.sqrt 3 * (-b ^ 2 + c ^ 2 + a * b - a * c)

def rateOne (p s : ℝ) : ℝ := -shearSq p s + 2 * p
def rateTwo (p s : ℝ) : ℝ := -shearSq p s - p + Real.sqrt 3 * s
def rateThree (p s : ℝ) : ℝ := -shearSq p s - p - Real.sqrt 3 * s

theorem curvature_factor (a b c : ℝ) :
    curvature a b c = (a - b - c) ^ 2 - 4 * b * c := by
  unfold curvature
  ring

theorem constraint_directional (p s a b c : ℝ) :
    2 * p * shearPlus p a b c + 2 * s * shearMinus s a b c +
      2 * (a - b - c) * (rateOne p s * a) +
      2 * (b - a - c) * (rateTwo p s * b) +
      2 * (c - a - b) * (rateThree p s * c) = 0 := by
  unfold shearPlus shearMinus rateOne rateTwo rateThree shearSq curvature
  ring

/-- This is an actual derivative along a solution, not only a polynomial identity. -/
theorem hasDerivAt_constraint
    {p s a b c : ℝ → ℝ} {t : ℝ}
    (hp : HasDerivAt p (shearPlus (p t) (a t) (b t) (c t)) t)
    (hs : HasDerivAt s (shearMinus (s t) (a t) (b t) (c t)) t)
    (ha : HasDerivAt a (rateOne (p t) (s t) * a t) t)
    (hb : HasDerivAt b (rateTwo (p t) (s t) * b t) t)
    (hc : HasDerivAt c (rateThree (p t) (s t) * c t) t) :
    HasDerivAt (fun u => constraint (p u) (s u) (a u) (b u) (c u)) 0 t := by
  convert ((hp.pow 2).add (hs.pow 2)).add
    (((ha.pow 2).add (hb.pow 2)).add (hc.pow 2) |>.sub
      ((((ha.mul hb).add (hb.mul hc)).add (hc.mul ha)).const_mul 2)) using 1 <;>
    first | rfl | (norm_num [constraint, shearSq, curvature, shearPlus, shearMinus,
      rateOne, rateTwo, rateThree]; ring)

theorem wall_product_directional (p s a b c : ℝ) :
    (rateOne p s * a) * b * c + a * (rateTwo p s * b) * c +
      a * b * (rateThree p s * c) = -3 * shearSq p s * (a * b * c) := by
  unfold rateOne rateTwo rateThree
  ring

theorem hasDerivAt_wall_product
    {p s a b c : ℝ → ℝ} {t : ℝ}
    (ha : HasDerivAt a (rateOne (p t) (s t) * a t) t)
    (hb : HasDerivAt b (rateTwo (p t) (s t) * b t) t)
    (hc : HasDerivAt c (rateThree (p t) (s t) * c t) t) :
    HasDerivAt (fun u => a u * b u * c u)
      (-3 * shearSq (p t) (s t) * (a t * b t * c t)) t := by
  convert (ha.mul hb).mul hc using 1 <;>
    first | rfl | (simp only [rateOne, rateTwo, rateThree, Pi.mul_apply]; ring)

theorem rateOne_eq (p s : ℝ) : rateOne p s = 1 - (p - 1) ^ 2 - s ^ 2 := by
  unfold rateOne shearSq
  ring

theorem rateTwo_eq (p s : ℝ) :
    rateTwo p s = 1 - (p + 1 / 2) ^ 2 - (s - Real.sqrt 3 / 2) ^ 2 := by
  have h : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  unfold rateTwo shearSq
  nlinarith

theorem rateThree_eq (p s : ℝ) :
    rateThree p s = 1 - (p + 1 / 2) ^ 2 - (s + Real.sqrt 3 / 2) ^ 2 := by
  have h : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  unfold rateThree shearSq
  nlinarith

theorem wall_rates_le_one (p s : ℝ) :
    rateOne p s ≤ 1 ∧ rateTwo p s ≤ 1 ∧ rateThree p s ≤ 1 := by
  rw [rateOne_eq, rateTwo_eq, rateThree_eq]
  exact ⟨by nlinarith [sq_nonneg (p - 1), sq_nonneg s],
    by nlinarith [sq_nonneg (p + 1 / 2), sq_nonneg (s - Real.sqrt 3 / 2)],
    by nlinarith [sq_nonneg (p + 1 / 2), sq_nonneg (s + Real.sqrt 3 / 2)]⟩

end

end BianchiIX
