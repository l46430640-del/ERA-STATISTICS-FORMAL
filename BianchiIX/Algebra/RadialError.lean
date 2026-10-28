import BianchiIX.Algebra.RadialArrival
import Mathlib.Tactic.Positivity

noncomputable section

namespace BianchiIX

theorem contracted_radius_error {s q r v : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    |s * q - v| ≤ |q - r| + |r - v| + |s - 1| * |v| := by
  have H := abs_sub_le (s * q) (s * v) v
  rw [← mul_sub, ← sub_one_mul, abs_mul, abs_mul, abs_of_nonneg hs] at H
  exact H.trans ((add_le_add (mul_le_of_le_one_left (abs_nonneg _) hs1) (le_refl _)).trans
    (add_le_add (abs_sub_le q r v) (le_refl _)))

/-- Combine radius drift with both moving endpoints before absorbing the initial strong component. -/
theorem core_radius_arrival_error {k U W K Q₀ s q r X v₀ v₁ : ℝ}
    (hk : 6 ≤ k) (hU : 0 ≤ U) (hW : 0 ≤ W) (hWk : W ≤ k)
    (hQ : |v₀| ≤ Q₀) (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hse : |s - 1| ≤ 8 * (U / k + W ^ 2 / k ^ 2))
    (hr : |r - v₀| ≤ 4 * (U / k + W ^ 2 / k ^ 2) * |v₀|)
    (hX : X ≤ k * |v₁| + 4 * k * U * |v₀|)
    (hd : |q - r| ≤ 256 * (X / k ^ 2 + (U + W) * ((2 * K) * Q₀) / k)) :
    |s * q - v₀| ≤ 256 * |v₁| / k + (1040 + 512 * K) * (U + W) * Q₀ / k := by
  have hk0 : 0 < k := by linarith only [hk]
  have hQ0 : 0 ≤ Q₀ := (abs_nonneg _).trans hQ
  have H := (contracted_radius_error hs hs1).trans
    (add_le_add (add_le_add hd hr) (mul_le_mul_of_nonneg_right hse (abs_nonneg _)))
  have hX' := mul_le_mul_of_nonneg_left
    (add_le_add (div_le_div_of_nonneg_right hX (sq_nonneg k))
      (le_refl ((U + W) * ((2 * K) * Q₀) / k))) (by norm_num : (0 : ℝ) ≤ 256)
  apply H.trans
  apply (add_le_add (add_le_add hX' (le_refl _)) (le_refl _)).trans
  have hUk := mul_le_mul_of_nonneg_left hQ (mul_nonneg hU hk0.le)
  have hWk' := mul_le_mul_of_nonneg_left hQ (mul_nonneg hW hk0.le)
  have hW2 := mul_le_mul_of_nonneg_right hWk (mul_nonneg hW (abs_nonneg v₀))
  have hUQk := mul_nonneg (mul_nonneg hU hQ0) hk0.le
  have hWQk := mul_nonneg (mul_nonneg hW hQ0) hk0.le
  apply (mul_le_mul_iff_of_pos_right (sq_pos_of_pos hk0)).mp
  field_simp
  nlinarith only [hUk, hWk', hW2, hUQk, hWQk]

end BianchiIX
