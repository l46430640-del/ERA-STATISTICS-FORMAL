import BianchiIX.Analysis.EntranceWallTerminalCorrection

noncomputable section

namespace BianchiIX

/-- The flow identity cancels the weak wall's leading logarithmic contraction. -/
theorem entrance_fixed_product_estimate {A B k u v w G βU βW Fr Fu Fv Fw : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hk : 1 ≤ k)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w ∧ w ≤ 1)
    (hG : |G| ≤ B * (u * v + (v * w) ^ 2 / k ^ 2))
    (hβU : |βU| ≤ 12 * k) (hβW : |βW + 1| ≤ 8 / k)
    (hFr : |Fr| ≤ 1 + 3 * A) (hFu : |Fu| ≤ A * v / k)
    (hFw : |Fw| ≤ A * (u * v + 2 * v ^ 2 * w) / k)
    (htransport : v * Fv + G * Fr + (u * βU) * Fu + (w * βW) * Fw = 0) :
    |v * Fv - w * Fw| ≤ (B * (1 + 3 * A) + 28 * A) * (u * v + (v * w) ^ 2 / k ^ 2) := by
  let H := u * v + (v * w) ^ 2 / k ^ 2
  have hk0 : 0 < k := by linarith
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have huvH : u * v ≤ H := le_add_of_nonneg_right (by positivity)
  have hfast : |(u * βU) * Fu| ≤ 12 * A * H := by
    rw [abs_mul, abs_mul, abs_of_nonneg hu]
    calc
      _ ≤ (u * (12 * k)) * (A * v / k) := mul_le_mul
        (mul_le_mul_of_nonneg_left hβU hu) hFu (abs_nonneg _) (by positivity)
      _ = 12 * A * (u * v) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left huvH (by positivity)
  have hslow : |w * (βW + 1) * Fw| ≤ 16 * A * H := by
    have hfirst : w * (u * v) / k ^ 2 ≤ u * v :=
      (div_le_self (by positivity [hw.1]) (one_le_pow₀ hk)).trans
        (mul_le_of_le_one_left (mul_nonneg hu hv) hw.2)
    have hsum : w * (u * v) / k ^ 2 + 2 * ((v * w) ^ 2 / k ^ 2) ≤ 2 * H := by
      dsimp [H]
      linarith only [hfirst, mul_nonneg hu hv]
    rw [abs_mul, abs_mul, abs_of_nonneg hw.1]
    calc
      _ ≤ (w * (8 / k)) * (A * (u * v + 2 * v ^ 2 * w) / k) := mul_le_mul
        (mul_le_mul_of_nonneg_left hβW hw.1) hFw (abs_nonneg _) (by positivity [hw.1])
      _ = (8 * A) * (w * (u * v) / k ^ 2 + 2 * ((v * w) ^ 2 / k ^ 2)) := by ring
      _ ≤ (8 * A) * (2 * H) := mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = _ := by ring
  have hrad : |G * Fr| ≤ B * (1 + 3 * A) * H := by
    rw [abs_mul]
    exact (mul_le_mul hG hFr (abs_nonneg _) (mul_nonneg hB hH)).trans_eq (by ring)
  have heq : v * Fv - w * Fw = -G * Fr - (u * βU) * Fu - w * (βW + 1) * Fw := by
    nlinarith only [htransport]
  rw [heq]
  calc
    _ ≤ |-G * Fr - (u * βU) * Fu| + |w * (βW + 1) * Fw| := abs_sub _ _
    _ ≤ |G * Fr| + |(u * βU) * Fu| + |w * (βW + 1) * Fw| := by
      simpa only [neg_mul, abs_neg] using add_le_add (abs_sub (-G * Fr) ((u * βU) * Fu)) (le_refl |w * (βW + 1) * Fw|)
    _ ≤ B * (1 + 3 * A) * H + 12 * A * H + 16 * A * H := add_le_add (add_le_add hrad hfast) hslow
    _ = _ := by dsimp [H]; ring

end BianchiIX
