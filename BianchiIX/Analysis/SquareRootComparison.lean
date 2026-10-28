import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section

namespace BianchiIX

/-- Relative quadratic error retains its order after taking square roots, including the zero scale. -/
theorem abs_sqrt_sub_sqrt_le_of_relative_error {a b A : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (H : |a - b| ≤ A * b) : |Real.sqrt a - Real.sqrt b| ≤ A * Real.sqrt b := by
  by_cases hb0 : b = 0
  · have Ha : a ≤ 0 := by simpa [hb0, abs_of_nonneg ha] using H
    have ha0 : a = 0 := le_antisymm Ha ha
    simp [ha0, hb0]
  have hbpos : 0 < Real.sqrt b := Real.sqrt_pos.mpr (lt_of_le_of_ne hb (Ne.symm hb0))
  have heq : |Real.sqrt a - Real.sqrt b| * (Real.sqrt a + Real.sqrt b) = |a - b| := by
    rw [← abs_of_nonneg (add_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)), ← abs_mul]
    congr 1
    nlinarith only [Real.sq_sqrt ha, Real.sq_sqrt hb]
  have HB : |Real.sqrt a - Real.sqrt b| * Real.sqrt b ≤ (A * Real.sqrt b) * Real.sqrt b := by
    calc
      _ ≤ |Real.sqrt a - Real.sqrt b| * (Real.sqrt a + Real.sqrt b) :=
        mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (Real.sqrt_nonneg a)) (abs_nonneg _)
      _ ≤ A * b := heq.le.trans H
      _ = A * (Real.sqrt b) ^ 2 := congrArg (fun x => A * x) (Real.sq_sqrt hb).symm
      _ = _ := by ring
  exact (mul_le_mul_iff_of_pos_right hbpos).mp HB

end BianchiIX
