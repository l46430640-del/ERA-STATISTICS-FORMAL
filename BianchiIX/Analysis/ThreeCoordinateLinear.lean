import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

noncomputable section

namespace BianchiIX

theorem three_coordinate_expansion (v : Fin 3 → ℝ) :
    v = v 0 • ![1, 0, 0] + v 1 • ![0, 1, 0] + v 2 • ![0, 0, 1] := by
  ext i
  fin_cases i <;> simp

theorem three_coordinate_linear_bound (A : (Fin 3 → ℝ) →L[ℝ] ℝ) (v : Fin 3 → ℝ) :
    |A v| ≤ |v 0| * |A ![1, 0, 0]| + |v 1| * |A ![0, 1, 0]| + |v 2| * |A ![0, 0, 1]| := by
  have hid : A v = v 0 * A ![1, 0, 0] + v 1 * A ![0, 1, 0] + v 2 * A ![0, 0, 1] := by
    conv_lhs => rw [three_coordinate_expansion v]
    simp only [map_add, map_smul, smul_eq_mul]
  rw [hid]
  simpa only [abs_mul] using
    (abs_add_le (v 0 * A ![1, 0, 0] + v 1 * A ![0, 1, 0]) (v 2 * A ![0, 0, 1])).trans
      (add_le_add (abs_add_le (v 0 * A ![1, 0, 0]) (v 1 * A ![0, 1, 0])) le_rfl)

end BianchiIX
