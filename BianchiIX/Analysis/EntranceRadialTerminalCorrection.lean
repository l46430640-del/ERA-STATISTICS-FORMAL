import BianchiIX.Analysis.EntranceTerminalWeights

noncomputable section

namespace BianchiIX

theorem entrance_radial_terminal_correction {A T k L P S U W X XU XW E : ℝ}
    (hA : 0 ≤ A) (hT : 0 ≤ T) (hk : 0 < k) (hL : 0 ≤ L) (hS : 0 ≤ S)
    (hU : 0 ≤ U) (hW : 0 ≤ W)
    (hsq : (U + W) ^ 2 ≤ 2 * (P + S))
    (hfast : k * L * (U + W) * U ≤ 6 * P)
    (hslow : (L / k) * (U + W) * W ≤ 3 * P + (L / k) * S)
    (hX : X ≤ 1 + 2 * A) (hXU : XU ≤ A * L) (hXW : XW ≤ A * L / k ^ 2)
    (hE : E ≤ T * ((U + W) ^ 2 / k ^ 2 * X + (U + W) / k * (U * XU + W * XW))) :
    E ≤ T * (2 + 13 * A) * (P + (1 + L / k) * S) / k ^ 2 := by
  have hrad : (U + W) ^ 2 / k ^ 2 * X ≤ 2 * (P + S) / k ^ 2 * (1 + 2 * A) :=
    (mul_le_mul_of_nonneg_left hX (by positivity)).trans
      (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hsq (sq_nonneg k)) (by positivity))
  have hwall : (U + W) / k * (U * XU + W * XW) ≤
      (A / k ^ 2) * (9 * P + (L / k) * S) := by
    calc
      _ ≤ (U + W) / k * (U * (A * L) + W * (A * L / k ^ 2)) :=
        mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left hXU hU)
          (mul_le_mul_of_nonneg_left hXW hW)) (by positivity)
      _ = (A / k ^ 2) * (k * L * (U + W) * U + (L / k) * (U + W) * W) := by
        field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left ((add_le_add hfast hslow).trans_eq (by ring)) (by positivity)
  have hnum : 2 * (P + S) * (1 + 2 * A) + A * (9 * P + (L / k) * S) ≤
      (2 + 13 * A) * (P + (1 + L / k) * S) := by
    calc
      _ = (2 + 13 * A) * (P + (1 + L / k) * S) -
          (9 * A * S + (2 + 12 * A) * (L / k) * S) := by ring
      _ ≤ _ := sub_le_self _ (by positivity)
  apply hE.trans
  calc
    _ ≤ T * (2 * (P + S) / k ^ 2 * (1 + 2 * A) + (A / k ^ 2) * (9 * P + (L / k) * S)) :=
      mul_le_mul_of_nonneg_left (add_le_add hrad hwall) hT
    _ = T * ((2 * (P + S) * (1 + 2 * A) + A * (9 * P + (L / k) * S)) / k ^ 2) := by ring
    _ ≤ T * (((2 + 13 * A) * (P + (1 + L / k) * S)) / k ^ 2) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hnum (sq_nonneg k)) hT
    _ = _ := by ring

end BianchiIX
