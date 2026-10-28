import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

noncomputable section

namespace BianchiIX

def arcoshGap (k v : ℝ) : ℝ := Real.arcosh (k / v) - Real.arcosh k

theorem sqrt_scaled_gap {k v : ℝ} (hk : 1 < k) (hv : 0 < v ∧ v < 1) :
    Real.sqrt ((k / v) ^ 2 - 1) = Real.sqrt (k ^ 2 - v ^ 2) / v := by
  have hpos : 0 ≤ k ^ 2 - v ^ 2 := by nlinarith only [hk, hv.1, hv.2]
  rw [show (k / v) ^ 2 - 1 = (k ^ 2 - v ^ 2) / v ^ 2 by field_simp [hv.1.ne'],
    Real.sqrt_div hpos, Real.sqrt_sq hv.1.le]

theorem hasDerivAt_arcoshGap {k v : ℝ} (hk : 1 < k) (hv : 0 < v ∧ v < 1) :
    HasDerivAt (fun r => arcoshGap r v)
      (1 / Real.sqrt (k ^ 2 - v ^ 2) - 1 / Real.sqrt (k ^ 2 - 1)) k := by
  have hkv : 1 < k / v := (one_lt_div hv.1).mpr (hv.2.trans hk)
  have H := ((Real.hasDerivAt_arcosh hkv).comp k ((hasDerivAt_id k).div_const v)).sub
    (Real.hasDerivAt_arcosh hk)
  convert! H using 1
  rw [sqrt_scaled_gap hk hv]
  field_simp [hv.1.ne']

theorem arcoshGap_bounds {k v : ℝ} (hk : 1 < k) (hv : 0 < v ∧ v < 1) :
    1 - v ≤ arcoshGap k v ∧ arcoshGap k v ≤ 2 * k / v := by
  have hk0 : 0 < k := by linarith
  have hkv : 1 < k / v := (one_lt_div hv.1).mpr (hv.2.trans hk)
  have hs : Real.sqrt (k ^ 2 - 1) ≤ Real.sqrt (k ^ 2 - v ^ 2) :=
    Real.sqrt_le_sqrt (by nlinarith only [hv.1, hv.2])
  have hlog := Real.log_le_log (by positivity : 0 < k + Real.sqrt (k ^ 2 - 1)) (add_le_add le_rfl hs)
  have hsplit : Real.arcosh (k / v) = Real.log (k + Real.sqrt (k ^ 2 - v ^ 2)) - Real.log v := by
    rw [Real.arcosh, sqrt_scaled_gap hk hv, ← add_div, Real.log_div (by positivity) hv.1.ne']
  constructor
  · have Hv := Real.log_le_sub_one_of_pos hv.1
    dsimp [arcoshGap]
    rw [hsplit, Real.arcosh]
    linarith only [hlog, Hv]
  · have Hlog := Real.log_le_sub_one_of_pos
      (by positivity : 0 < k / v + Real.sqrt ((k / v) ^ 2 - 1))
    have Hsqrt : Real.sqrt ((k / v) ^ 2 - 1) ≤ k / v :=
      Real.sqrt_le_iff.mpr ⟨(div_pos hk0 hv.1).le, by linarith⟩
    have Hnonneg := Real.arcosh_nonneg hk.le
    dsimp [arcoshGap]
    simp only [Real.arcosh] at Hnonneg ⊢
    simp only [div_eq_mul_inv] at Hlog Hsqrt ⊢
    linarith only [Hlog, Hsqrt, Hnonneg]

theorem arcoshGap_derivative_bound {k v : ℝ} (hk : 2 ≤ k) (hv : 0 < v ∧ v < 1) :
    |1 / Real.sqrt (k ^ 2 - v ^ 2) - 1 / Real.sqrt (k ^ 2 - 1)| ≤ 4 / k := by
  have hk0 : 0 < k := by linarith
  have hV : k / 2 ≤ Real.sqrt (k ^ 2 - v ^ 2) :=
    Real.le_sqrt_of_sq_le (by nlinarith only [hk, hv.1, hv.2])
  have hW : k / 2 ≤ Real.sqrt (k ^ 2 - 1) := Real.le_sqrt_of_sq_le (by nlinarith only [hk])
  have hbound {x : ℝ} (hx : k / 2 ≤ x) : |1 / x| ≤ 2 / k := by
    have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hx
    rw [abs_of_pos (div_pos zero_lt_one hx0)]
    exact ((div_le_div_of_nonneg_left (by norm_num) (by positivity : 0 < k / 2) hx).trans_eq (by ring))
  exact (abs_sub _ _).trans ((add_le_add (hbound hV) (hbound hW)).trans_eq (by ring))

end BianchiIX
