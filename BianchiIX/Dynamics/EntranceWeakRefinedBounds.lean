import BianchiIX.Dynamics.EntranceWeakQuadraticBounds

noncomputable section

namespace BianchiIX

set_option maxHeartbeats 500000 in
/-- The strengthened ordinary numerator bounds used by (C.23), including zero stable walls. -/
theorem exists_entranceWeakNumerator_refined_bounds :
    ∃ C > (0 : ℝ), ∀ (k : ℝ) (y : ProjectiveState), 7 / 4 ≤ k → entranceRegion k y →
      k * (y 1 + y 3) ^ 2 ≤ 1 →
      let b := y 1 + y 3
      let L := fderiv ℝ entranceWeakNumerator y
      |entranceWeakNumerator y| ≤ C * (y 1 * b + y 3 ^ 2 / k ^ 2) ∧
      |L (Pi.single 0 1)| ≤ C * b ^ 2 / k ^ 3 ∧
      |L (Pi.single 1 1)| ≤ C * b ∧
      |L (Pi.single 3 1)| ≤ C * (y 1 + y 3 / k ^ 2) := by
  obtain ⟨R, hR, HR⟩ := exists_entranceWeakRemainder_bounds
  refine ⟨40 + 4 * R, by positivity, ?_⟩
  intro k y hk hy hsmall
  let b := y 1 + y 3
  have hb : 0 ≤ b := add_nonneg hy.2.2.1.1 hy.2.2.2.2.1
  have hb1 : b ≤ 1 := by dsimp [b]; linarith [hy.2.2.1.2, hy.2.2.2.2.2]
  have hu0 := hy.2.2.1.1
  have hw0 := hy.2.2.2.2.1
  have hk1 : 1 ≤ k := by linarith
  have hk0 : 0 < k := by linarith
  have hk2 : 1 ≤ k ^ 2 := one_le_pow₀ hk1
  have hm : 2 < y 0 := by linarith [(entranceRegion_phase hk hy).1]
  have hu : |y 1| < 1 / 200 := by rw [abs_of_nonneg hu0]; linarith [hy.2.2.1.2]
  have hw : |y 3| < 1 / 200 := by rw [abs_of_nonneg hw0]; linarith [hy.2.2.2.2.2]
  have hb2 : b ^ 2 ≤ 1 := by nlinarith only [hb, hb1]
  have hb3 : b ^ 3 ≤ b := by
    nlinarith only [mul_le_mul_of_nonneg_right hb2 hb]
  have hb4 : b ^ 4 ≤ b ^ 2 := by
    nlinarith only [mul_le_mul_of_nonneg_right hb2 (sq_nonneg b)]
  have hquad : b ^ 2 ≤ 2 * y 1 * b + y 3 ^ 2 := by
    dsimp [b]
    nlinarith only [sq_nonneg (y 1)]
  have hvalscale : b ^ 4 / k ^ 2 ≤ 2 * y 1 * b + y 3 ^ 2 / k ^ 2 := by
    calc
      _ ≤ (2 * y 1 * b + y 3 ^ 2) / k ^ 2 := div_le_div_of_nonneg_right (hb4.trans hquad) (sq_nonneg k)
      _ = (2 * y 1 * b) / k ^ 2 + y 3 ^ 2 / k ^ 2 := by ring
      _ ≤ _ := add_le_add (div_le_self (by positivity) hk2) le_rfl
  have hphasescale : b ^ 4 / k ^ 2 ≤ b ^ 2 / k ^ 3 := by
    calc
      _ = (k * b ^ 2) * (b ^ 2 / k ^ 3) := by field_simp
      _ ≤ 1 * (b ^ 2 / k ^ 3) := mul_le_mul_of_nonneg_right hsmall (by positivity)
      _ = _ := one_mul _
  have hUscale : b ^ 3 / k ^ 2 ≤ b := (div_le_self (by positivity) hk2).trans hb3
  have hWscale : b ^ 3 / k ^ 2 ≤ y 1 + y 3 / k ^ 2 := by
    calc
      _ ≤ b / k ^ 2 := div_le_div_of_nonneg_right hb3 (sq_nonneg k)
      _ = y 1 / k ^ 2 + y 3 / k ^ 2 := by dsimp [b]; ring
      _ ≤ _ := add_le_add (div_le_self hu0 hk2) le_rfl
  obtain ⟨hphase, hwalls⟩ := HR k y hk hy
  have hE0 : |entranceWeakRemainder y| ≤ R * b ^ 4 / k ^ 2 := by
    linarith only [hphase, abs_nonneg (fderiv ℝ entranceWeakRemainder y (Pi.single 0 1))]
  have hEM : |fderiv ℝ entranceWeakRemainder y (Pi.single 0 1)| ≤ R * b ^ 4 / k ^ 2 := by
    linarith only [hphase, abs_nonneg (entranceWeakRemainder y)]
  have hEU : |fderiv ℝ entranceWeakRemainder y (Pi.single 1 1)| ≤ R * b ^ 3 / k ^ 2 := by
    linarith only [hwalls, abs_nonneg (fderiv ℝ entranceWeakRemainder y (Pi.single 3 1))]
  have hEW : |fderiv ℝ entranceWeakRemainder y (Pi.single 3 1)| ≤ R * b ^ 3 / k ^ 2 := by
    linarith only [hwalls, abs_nonneg (fderiv ℝ entranceWeakRemainder y (Pi.single 1 1))]
  have hmul (a c : ℝ) (ha : a ≤ c) : R * a ≤ R * c := mul_le_mul_of_nonneg_left ha hR.le
  have hE0' : |entranceWeakRemainder y| ≤ R * (2 * y 1 * b + y 3 ^ 2 / k ^ 2) :=
    hE0.trans ((by ring : R * b ^ 4 / k ^ 2 = R * (b ^ 4 / k ^ 2)).le.trans (hmul _ _ hvalscale))
  have hEM' : |fderiv ℝ entranceWeakRemainder y (Pi.single 0 1)| ≤ R * b ^ 2 / k ^ 3 := by
    calc
      _ ≤ R * b ^ 4 / k ^ 2 := hEM
      _ = R * (b ^ 4 / k ^ 2) := by ring
      _ ≤ R * (b ^ 2 / k ^ 3) := hmul _ _ hphasescale
      _ = _ := by ring
  have hEU' : |fderiv ℝ entranceWeakRemainder y (Pi.single 1 1)| ≤ R * b := by
    calc
      _ ≤ R * b ^ 3 / k ^ 2 := hEU
      _ = R * (b ^ 3 / k ^ 2) := by ring
      _ ≤ _ := hmul _ _ hUscale
  have hEW' : |fderiv ℝ entranceWeakRemainder y (Pi.single 3 1)| ≤ R * (y 1 + y 3 / k ^ 2) := by
    calc
      _ ≤ R * b ^ 3 / k ^ 2 := hEW
      _ = R * (b ^ 3 / k ^ 2) := by ring
      _ ≤ _ := hmul _ _ hWscale
  obtain ⟨hQ, hQM, hQU, hQW⟩ := entranceWeakQuadratic_bounds hk hy
  have hd := entranceWeakNumerator_expansion_fderiv hm hu hw
  dsimp only
  rw [entranceWeakNumerator_quadratic_expansion hm.le hu hw, hd, hd, hd]
  refine ⟨((abs_add_le _ _).trans (add_le_add hQ hE0')).trans ?_,
    ((abs_add_le _ _).trans (add_le_add hQM hEM')).trans ?_,
    ((abs_add_le _ _).trans (add_le_add hQU hEU')).trans ?_,
    ((abs_add_le _ _).trans (add_le_add hQW hEW')).trans ?_⟩
  · change y 1 * b + 4 * y 3 ^ 2 / k ^ 2 + R * (2 * y 1 * b + y 3 ^ 2 / k ^ 2) ≤ _
    have hUb : 0 ≤ y 1 * b := mul_nonneg hu0 hb
    have htail : 0 ≤ y 3 ^ 2 / k ^ 2 := by positivity
    have hc (a c : ℝ) (ha : 0 ≤ a) (hc : 0 ≤ c) : a + 4 * c + R * (2 * a + c) ≤ (40 + 4 * R) * (a + c) := by
      nlinarith only [ha, hc, mul_nonneg hR.le ha, mul_nonneg hR.le hc]
    convert! hc _ _ hUb htail using 1
    ring
  · calc
      _ = (32 + R) * b ^ 2 / k ^ 3 := by ring
      _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith only [hR]) (sq_nonneg b)) (by positivity)
  · change 2 * b + R * b ≤ _
    nlinarith only [hb, mul_nonneg hR.le hb]
  · change y 1 + 8 * y 3 / k ^ 2 + R * (y 1 + y 3 / k ^ 2) ≤ _
    have htail : 0 ≤ y 3 / k ^ 2 := by positivity
    have hc (a c : ℝ) (ha : 0 ≤ a) (hc : 0 ≤ c) : a + 8 * c + R * (a + c) ≤ (40 + 4 * R) * (a + c) := by
      nlinarith only [ha, hc, mul_nonneg hR.le ha, mul_nonneg hR.le hc]
    convert! hc _ _ hu0 htail using 1
    ring

end BianchiIX
