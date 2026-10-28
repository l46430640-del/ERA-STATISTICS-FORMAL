import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section

namespace BianchiIX

/-- A primitive of the upper bound for the signed row sums. -/
def coreGrowthPrimitive (k z : ℝ) : ℝ :=
  2 * Real.arctan (Real.sinh z) + 24 * ((1 / 10000) / k) * z

def coreVariationBound : ℝ := Real.exp (2 * Real.pi + 48 / 10000)

theorem hasDerivAt_coreGrowthPrimitive (k z : ℝ) :
    HasDerivAt (coreGrowthPrimitive k) (2 / Real.cosh z + 24 * ((1 / 10000) / k)) z := by
  have H := (((Real.hasDerivAt_arctan (Real.sinh z)).comp z (Real.hasDerivAt_sinh z)).const_mul 2).add
    ((hasDerivAt_id z).const_mul (24 * ((1 / 10000) / k)))
  apply H.congr_deriv
  rw [← Real.cosh_sq']
  field_simp [ne_of_gt (Real.cosh_pos z)]

theorem core_log_bound {k : ℝ} (hk : 6 ≤ k) : Real.log (4 * k) ≤ k := by
  have hk0 : 0 ≤ k := by linarith
  apply (Real.log_le_iff_le_exp (by positivity : 0 < 4 * k)).mpr
  have H := Real.quadratic_le_exp_of_nonneg hk0
  nlinarith only [hk, H, sq_nonneg (k - 6)]

theorem coreGrowthPrimitive_difference {k a b : ℝ} (hk : 6 ≤ k)
    (ha : |a| ≤ Real.log (4 * k)) (hb : |b| ≤ Real.log (4 * k)) :
    coreGrowthPrimitive k b - coreGrowthPrimitive k a ≤ 2 * Real.pi + 48 / 10000 := by
  have hk0 : 0 < k := by linarith
  have hlen : b - a ≤ 2 * k := by
    have H := core_log_bound hk
    have Ha := (abs_le.mp ha).1
    have Hb := (abs_le.mp hb).2
    linarith only [H, Ha, Hb]
  have hlinear : 24 * ((1 / 10000) / k) * (b - a) ≤ 48 / 10000 := by
    calc
      _ ≤ 24 * ((1 / 10000) / k) * (2 * k) := mul_le_mul_of_nonneg_left hlen (by positivity)
      _ = 48 / 10000 := by field_simp; ring
  have hatan : 2 * (Real.arctan (Real.sinh b) - Real.arctan (Real.sinh a)) ≤ 2 * Real.pi := by
    linarith only [Real.arctan_lt_pi_div_two (Real.sinh b), Real.neg_pi_div_two_lt_arctan (Real.sinh a)]
  unfold coreGrowthPrimitive
  linarith only [hlinear, hatan]

theorem coreGrowthPrimitive_exp_difference {k a b : ℝ} (hk : 6 ≤ k)
    (ha : |a| ≤ Real.log (4 * k)) (hb : |b| ≤ Real.log (4 * k)) :
    Real.exp (coreGrowthPrimitive k b - coreGrowthPrimitive k a) ≤ coreVariationBound :=
  Real.exp_le_exp.mpr (coreGrowthPrimitive_difference hk ha hb)

end BianchiIX
