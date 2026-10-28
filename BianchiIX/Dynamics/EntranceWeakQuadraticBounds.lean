import BianchiIX.Dynamics.EntranceWeakQuadraticDerivative

noncomputable section

namespace BianchiIX

theorem entranceWeakQuadratic_bounds {k : ℝ} {y : ProjectiveState}
    (hk : 7 / 4 ≤ k) (hy : entranceRegion k y) :
    let b := y 1 + y 3
    let L := fderiv ℝ entranceWeakQuadratic y
    |entranceWeakQuadratic y| ≤ y 1 * b + 4 * y 3 ^ 2 / k ^ 2 ∧
    |L (Pi.single 0 1)| ≤ 32 * b ^ 2 / k ^ 3 ∧
    |L (Pi.single 1 1)| ≤ 2 * b ∧
    |L (Pi.single 3 1)| ≤ y 1 + 8 * y 3 / k ^ 2 := by
  have hm : 2 ≤ y 0 := by linarith [(entranceRegion_phase hk hy).1]
  have hk0 : 0 < k := by linarith
  have hL0 : 0 < y 0 + 1 := by linarith
  have hL : k / 2 ≤ y 0 + 1 := by linarith [(entranceRegion_phase hk hy).1]
  have hu0 := hy.2.2.1.1
  have hw0 := hy.2.2.2.2.1
  have hi0 : 0 ≤ 1 / (y 0 + 1) ^ 2 := by positivity
  have hi1 : 1 / (y 0 + 1) ^ 2 ≤ 1 := (div_le_one (by positivity)).mpr (by nlinarith only [hm])
  have h40 : 0 ≤ 4 / (y 0 + 1) ^ 2 := by positivity
  have h41 : 4 / (y 0 + 1) ^ 2 ≤ 1 := (div_le_one (by positivity)).mpr (by nlinarith only [hm])
  have hA : |1 - 1 / (y 0 + 1) ^ 2| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hC : |-1 + 4 / (y 0 + 1) ^ 2| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hscale (q : ℝ) (hq : 0 ≤ q) (n : ℕ) : q / (y 0 + 1) ^ n ≤ 2 ^ n * q / k ^ n := by
    calc
      _ ≤ q / (k / 2) ^ n := div_le_div_of_nonneg_left hq (by positivity) (pow_le_pow_left₀ (by positivity) hL n)
      _ = _ := by simp only [div_pow]; field_simp
  have hd := (entranceWeakQuadratic_differential hL0.ne').2
  have h0 : fderiv ℝ entranceWeakQuadratic y (Pi.single 0 1) =
      (2 * y 1 ^ 2 - 8 * y 1 * y 3 + 2 * y 3 ^ 2) / (y 0 + 1) ^ 3 := by simp [hd]
  have h1 : fderiv ℝ entranceWeakQuadratic y (Pi.single 1 1) =
      2 * (1 - 1 / (y 0 + 1) ^ 2) * y 1 + (-1 + 4 / (y 0 + 1) ^ 2) * y 3 := by simp [hd]
  have h3 : fderiv ℝ entranceWeakQuadratic y (Pi.single 3 1) =
      (-1 + 4 / (y 0 + 1) ^ 2) * y 1 - 2 * y 3 / (y 0 + 1) ^ 2 := by simp [hd]
  dsimp only
  rw [h0, h1, h3]
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold entranceWeakQuadratic
    calc
      _ ≤ |(1 - 1 / (y 0 + 1) ^ 2) * y 1 ^ 2| + |(-1 + 4 / (y 0 + 1) ^ 2) * y 1 * y 3| +
          |y 3 ^ 2 / (y 0 + 1) ^ 2| := (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ y 1 ^ 2 + y 1 * y 3 + 4 * y 3 ^ 2 / k ^ 2 := by
        simp only [abs_mul, abs_div, abs_of_nonneg hu0, abs_of_nonneg hw0,
          abs_of_nonneg (sq_nonneg (y 1)), abs_of_nonneg (sq_nonneg (y 3)), abs_of_nonneg (sq_nonneg (y 0 + 1))]
        exact add_le_add (add_le_add (by simpa using mul_le_mul_of_nonneg_right hA (sq_nonneg (y 1)))
          (by simpa using mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC hu0) hw0))
          (by simpa only [show (2 : ℝ) ^ 2 = 4 by norm_num] using hscale (y 3 ^ 2) (sq_nonneg _) 2)
      _ = _ := by ring
  · have hnum : |2 * y 1 ^ 2 - 8 * y 1 * y 3 + 2 * y 3 ^ 2| ≤ 4 * (y 1 + y 3) ^ 2 := by
      calc
        _ ≤ |2 * y 1 ^ 2| + |8 * y 1 * y 3| + |2 * y 3 ^ 2| :=
          (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
        _ = 2 * y 1 ^ 2 + 8 * y 1 * y 3 + 2 * y 3 ^ 2 := by
          rw [abs_of_nonneg (by positivity : 0 ≤ 2 * y 1 ^ 2), abs_of_nonneg (by positivity : 0 ≤ 8 * y 1 * y 3),
            abs_of_nonneg (by positivity : 0 ≤ 2 * y 3 ^ 2)]
        _ ≤ _ := by nlinarith only [sq_nonneg (y 1), sq_nonneg (y 3)]
    rw [abs_div, abs_of_pos (pow_pos hL0 3)]
    calc
      _ ≤ (4 * (y 1 + y 3) ^ 2) / (y 0 + 1) ^ 3 := div_le_div_of_nonneg_right hnum (by positivity)
      _ ≤ 2 ^ 3 * (4 * (y 1 + y 3) ^ 2) / k ^ 3 := hscale _ (by positivity) 3
      _ = _ := by ring
  · calc
      _ ≤ |2 * (1 - 1 / (y 0 + 1) ^ 2) * y 1| + |(-1 + 4 / (y 0 + 1) ^ 2) * y 3| := abs_add_le _ _
      _ ≤ 2 * y 1 + y 3 := by
        simp only [abs_mul, abs_of_nonneg hu0, abs_of_nonneg hw0]
        rw [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        exact add_le_add (by simpa using mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hA (by norm_num : (0 : ℝ) ≤ 2)) hu0)
          (by simpa using mul_le_mul_of_nonneg_right hC hw0)
      _ ≤ _ := by linarith only [hw0]
  · calc
      _ ≤ |(-1 + 4 / (y 0 + 1) ^ 2) * y 1| + |2 * y 3 / (y 0 + 1) ^ 2| := abs_sub _ _
      _ ≤ y 1 + 8 * y 3 / k ^ 2 := by
        rw [abs_mul, abs_of_nonneg hu0, abs_of_nonneg (by positivity : 0 ≤ 2 * y 3 / (y 0 + 1) ^ 2)]
        exact add_le_add (by simpa using mul_le_mul_of_nonneg_right hC hu0)
          ((hscale (2 * y 3) (by positivity) 2).trans_eq (by ring))

end BianchiIX
