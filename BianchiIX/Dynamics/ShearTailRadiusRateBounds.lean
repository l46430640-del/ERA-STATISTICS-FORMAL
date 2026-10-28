import BianchiIX.Dynamics.ShearTailRadiusDifferential

noncomputable section

namespace BianchiIX

/-- Both polynomial numerator bounds retain the radius energy before division by the radius. -/
theorem shearTailRadius_numerator_bounds {a L : ℝ} {z v : NormalizedState}
    (ha : 0 < a ∧ a ≤ 1 / 256) (hL : 0 ≤ L)
    (hc : stateConstraint z = 1) (hr : shearTailRegion a z)
    (hn : 0 ≤ z 2 ∧ 0 ≤ z 3 ∧ 0 ≤ z 4)
    (hv : normalizedConstraintDifferential z v = 0) (hs : |v 1| ≤ 5)
    (hw : |v 2| ≤ z 2 * L ∧ |v 3| ≤ z 3 * L ∧ |v 4| ≤ z 4 * L) :
    |shearTailRadiusNumerator z| ≤ 128 * a ^ 2 * shearTailRadiusEnergy z ∧
    |shearTailRadiusNumeratorDifferential z v| ≤ 4096 * a * shearTailRadiusEnergy z * (1 + a * L) := by
  let E := shearTailRadiusEnergy z
  let B := 1 + a * L
  let d := z 3 - z 4
  let dv := v 3 - v 4
  let Q := curvature (z 2) (z 3) (z 4)
  let R := shearTailRadius z
  have ha0 : 0 ≤ a := ha.1.le
  have hn0 : 0 ≤ z 2 := hn.1
  have ha1 : a ≤ 1 := by linarith only [ha.2]
  have ha2 : a ^ 2 ≤ a := by nlinarith only [ha.1, ha1]
  have HE := shearTailRadius_energy_bounds ⟨ha.1, ha1⟩ hr hn
  have hE : 0 ≤ E := HE.1
  have hnE : z 2 ≤ E := by dsimp only [E, shearTailRadiusEnergy]; nlinarith only [sq_nonneg (z 3), sq_nonneg (z 4)]
  have hB : 0 ≤ B := by dsimp only [B]; positivity [ha.1]
  have HB1 : a * E ≤ a * E * B := by
    dsimp only [B]
    nlinarith only [mul_nonneg (mul_nonneg ha.1.le hE) (mul_nonneg ha.1.le hL)]
  have HBL : a ^ 2 * E * L ≤ a * E * B := by
    dsimp only [B]
    nlinarith only [mul_nonneg ha.1.le hE]
  have hx : z 3 ≤ a := hr.2.2.2.2.1.trans ha2
  have hy : z 4 ≤ a := by linarith only [hr.2.2.2.2.2, ha.1]
  have hs0 : 0 < z 1 := by linarith only [hr.2.1, ha.1]
  have hR : 0 < R := shearTailRadius_pos hs0.ne'
  have HR := shearTailRadius_region_bounds ⟨ha.1, ha1⟩ hr hn.2
  have HR2 : R ^ 2 ≤ 16 * a ^ 2 := by
    nlinarith only [pow_le_pow_left₀ hR.le HR.2 2]
  have HRS : z 1 ^ 2 + d ^ 2 = R ^ 2 := (shearTailRadius_sq z).symm
  have Hd : |d| ≤ 2 * a := (abs_sub _ _).trans (by
    rw [abs_of_nonneg hn.2.1, abs_of_nonneg hn.2.2]
    linarith only [hx, hy])
  have Hd2 : d ^ 2 ≤ 2 * E := by
    dsimp only [d, E, shearTailRadiusEnergy]
    nlinarith only [sq_nonneg (z 3 + z 4), hn.1]
  have Hsum2 : (z 3 + z 4) ^ 2 ≤ 2 * E := by
    dsimp only [E, shearTailRadiusEnergy]
    nlinarith only [sq_nonneg (z 3 - z 4), hn.1]
  have Hdv : |dv| ≤ (z 3 + z 4) * L := by
    have H := (abs_sub (v 3) (v 4)).trans (add_le_add hw.2.1 hw.2.2)
    dsimp only [dv]
    nlinarith only [H]
  have Hdv' : |dv| ≤ 2 * a * L := Hdv.trans (by
    have H := mul_le_mul_of_nonneg_right (show z 3 + z 4 ≤ 2 * a by linarith only [hx, hy]) hL
    exact H)
  have Hdd : |d * dv| ≤ 2 * E * L := by
    have Hdx : |d| ≤ z 3 + z 4 := by
      simpa only [d, abs_of_nonneg hn.2.1, abs_of_nonneg hn.2.2] using abs_sub (z 3) (z 4)
    rw [abs_mul]
    have H := mul_le_mul Hdx Hdv (abs_nonneg _) (add_nonneg hn.2.1 hn.2.2)
    nlinarith only [H, mul_le_mul_of_nonneg_right Hsum2 hL]
  obtain ⟨HQ, HdQ, _⟩ := shearTail_polynomial_variation_bounds hL hn hw
  have HQ' : |Q| ≤ 6 * E := by linarith only [HQ, HE.2.2]
  have HdQ' : |shearTailCurvatureDifferential z v| ≤ 12 * E * L := by
    nlinarith only [HdQ, mul_le_mul_of_nonneg_right HE.2.2 hL]
  obtain ⟨HD, Hp⟩ := shearTailRadius_differential_bounds ha hL hr hn hv hs hw
  have HD' : |z 1 * v 1 + d * dv| ≤ 160 * a * B := by
    have he : z 1 * v 1 + d * dv = R * shearTailRadiusDifferential z v := by
      dsimp only [shearTailRadiusDifferential, R, d, dv]
      field_simp [show shearTailRadius z ≠ 0 from hR.ne']
    rw [he, abs_mul, abs_of_pos hR]
    have H := mul_le_mul HR.2 HD (abs_nonneg _) (by positivity [ha.1] : 0 ≤ 4 * a)
    nlinarith only [H]
  obtain ⟨_, _, _, _, _, HAl, HAu⟩ := shearTail_constraint_bounds ha
    (by linarith only [hr.1]) ⟨hr.2.1, hr.2.2.1⟩ ⟨hn.1, hr.2.2.2.1⟩
    ⟨hn.2.1, hr.2.2.2.2.1⟩ ⟨hn.2.2, hr.2.2.2.2.2⟩ hc
  have hA : 0 ≤ 1 + z 0 := (by positivity : 0 ≤ a ^ 2 / 10).trans HAl
  have hroot : |Real.sqrt (3 : ℝ)| ≤ 2 := by
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    nlinarith only [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg (3 : ℝ)]
  have Hs : |z 1| ≤ 3 * a := by rw [abs_of_pos hs0]; exact hr.2.2.1
  have V1 : |Q * (z 1 ^ 2 + d ^ 2)| ≤ 96 * a ^ 2 * E := by
    rw [HRS, abs_mul, abs_of_nonneg (sq_nonneg R)]
    have H := mul_le_mul HQ' HR2 (sq_nonneg R) (by positivity : 0 ≤ 6 * E)
    nlinarith only [H]
  have V2 : |(1 + z 0) * d ^ 2| ≤ 12 * a ^ 2 * E := by
    rw [abs_mul, abs_of_nonneg hA, abs_of_nonneg (sq_nonneg d)]
    have H := mul_le_mul HAu Hd2 (sq_nonneg d) (by positivity : 0 ≤ 6 * a ^ 2)
    nlinarith only [H]
  have V3 : |Real.sqrt 3 * z 2 * z 1 * d| ≤ 12 * a ^ 2 * E := by
    simp only [abs_mul, abs_of_nonneg hn.1]
    calc
      _ ≤ 2 * E * (3 * a) * (2 * a) := by gcongr
      _ = _ := by ring
  have VG : |shearTailRadiusNumerator z| ≤ 128 * a ^ 2 * E := by
    have H := abs_add_le (Q * (z 1 ^ 2 + d ^ 2) - (1 + z 0) * d ^ 2) (Real.sqrt 3 * z 2 * z 1 * d)
    have H' := abs_sub (Q * (z 1 ^ 2 + d ^ 2)) ((1 + z 0) * d ^ 2)
    change |Q * (z 1 ^ 2 + d ^ 2) - (1 + z 0) * d ^ 2 + Real.sqrt 3 * z 2 * z 1 * d| ≤ _
    nlinarith only [H, H', V1, V2, V3, mul_nonneg (sq_nonneg a) hE]
  have D1 : |shearTailCurvatureDifferential z v * (z 1 ^ 2 + d ^ 2)| ≤ 192 * a * E * B := by
    rw [HRS, abs_mul, abs_of_nonneg (sq_nonneg R)]
    have H := mul_le_mul HdQ' HR2 (sq_nonneg R) (by positivity : 0 ≤ 12 * E * L)
    nlinarith only [H, HBL]
  have D2 : |2 * Q * (z 1 * v 1 + d * dv)| ≤ 1920 * a * E * B := by
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have H := mul_le_mul HQ' HD' (abs_nonneg _) (by positivity : 0 ≤ 6 * E)
    nlinarith only [H]
  have D3 : |v 0 * d ^ 2| ≤ 80 * a * E * B := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg d)]
    have H := mul_le_mul Hp Hd2 (sq_nonneg d) (by positivity [ha.1] : 0 ≤ 40 * a * B)
    nlinarith only [H]
  have D4 : |2 * (1 + z 0) * d * dv| ≤ 24 * a * E * B := by
    rw [mul_assoc (2 * (1 + z 0)), abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_nonneg hA]
    have H := mul_le_mul HAu Hdd (abs_nonneg _) (by positivity : 0 ≤ 6 * a ^ 2)
    nlinarith only [H, HBL]
  have D5 : |Real.sqrt 3 * (v 2 * z 1 * d + z 2 * v 1 * d + z 2 * z 1 * dv)| ≤ 44 * a * E * B := by
    have H1 : |v 2 * z 1 * d| ≤ 6 * a ^ 2 * E * L := by
      simp only [abs_mul]
      calc
        _ ≤ (E * L) * (3 * a) * (2 * a) := by gcongr; exact hw.1.trans (mul_le_mul_of_nonneg_right hnE hL)
        _ = _ := by ring
    have H2 : |z 2 * v 1 * d| ≤ 10 * a * E := by
      simp only [abs_mul, abs_of_nonneg hn.1]
      calc
        _ ≤ E * 5 * (2 * a) := by gcongr
        _ = _ := by ring
    have H3 : |z 2 * z 1 * dv| ≤ 6 * a ^ 2 * E * L := by
      simp only [abs_mul, abs_of_nonneg hn.1]
      calc
        _ ≤ E * (3 * a) * (2 * a * L) := by gcongr
        _ = _ := by ring
    have H := abs_add_three (v 2 * z 1 * d) (z 2 * v 1 * d) (z 2 * z 1 * dv)
    have Hsum : |v 2 * z 1 * d + z 2 * v 1 * d + z 2 * z 1 * dv| ≤ 22 * a * E * B := by
      nlinarith only [H, H1, H2, H3, HBL, HB1]
    rw [abs_mul]
    have Hprod := mul_le_mul hroot Hsum (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith only [Hprod]
  refine ⟨VG, ?_⟩
  let t1 := shearTailCurvatureDifferential z v * (z 1 ^ 2 + d ^ 2)
  let t2 := 2 * Q * (z 1 * v 1 + d * dv)
  let t3 := v 0 * d ^ 2
  let t4 := 2 * (1 + z 0) * d * dv
  let t5 := Real.sqrt 3 * (v 2 * z 1 * d + z 2 * v 1 * d + z 2 * z 1 * dv)
  have H := abs_add_le (t1 + t2 - t3 - t4) t5
  have H4 := abs_sub (t1 + t2 - t3) t4
  have H3 := abs_sub (t1 + t2) t3
  have H2 := abs_add_le t1 t2
  change |t1 + t2 - t3 - t4 + t5| ≤ 4096 * a * E * B
  nlinarith only [H, H4, H3, H2, D1, D2, D3, D4, D5, mul_nonneg (mul_nonneg ha.1.le hE) hB]

/-- Dividing by the controlled radius preserves the wall energy in both the rate and its response. -/
theorem shearTailRadius_rate_bounds {a L : ℝ} {z v : NormalizedState}
    (ha : 0 < a ∧ a ≤ 1 / 256) (hL : 0 ≤ L)
    (hc : stateConstraint z = 1) (hr : shearTailRegion a z)
    (hn : 0 ≤ z 2 ∧ 0 ≤ z 3 ∧ 0 ≤ z 4)
    (hv : normalizedConstraintDifferential z v = 0) (hs : |v 1| ≤ 5)
    (hw : |v 2| ≤ z 2 * L ∧ |v 3| ≤ z 3 * L ∧ |v 4| ≤ z 4 * L) :
    |shearTailRadiusRate z| ≤ 256 * a * shearTailRadiusEnergy z ∧
    |shearTailRadiusRateDifferential z v| ≤ 32768 * shearTailRadiusEnergy z * (1 + a * L) := by
  let E := shearTailRadiusEnergy z
  let B := 1 + a * L
  have hE : 0 ≤ E := by dsimp only [E, shearTailRadiusEnergy]; positivity [hn.1]
  have hB : 0 ≤ B := by dsimp only [B]; positivity [ha.1]
  have hs0 : 0 < z 1 := by linarith only [hr.2.1, ha.1]
  have hR := shearTailRadius_pos hs0.ne'
  have HR := shearTailRadius_region_bounds ⟨ha.1, by linarith only [ha.2]⟩ hr hn.2
  obtain ⟨HG, HDG⟩ := shearTailRadius_numerator_bounds ha hL hc hr hn hv hs hw
  have HD := (shearTailRadius_differential_bounds ha hL hr hn hv hs hw).1
  constructor
  · rw [shearTailRadiusRate_eq_quotient, abs_div, abs_of_pos hR]
    calc
      _ ≤ (128 * a ^ 2 * E) / (a / 2) := div_le_div₀ (by positivity) HG (by positivity [ha.1]) HR.1
      _ = _ := by field_simp [ha.1.ne']; ring
  · have H1 : |shearTailRadiusNumeratorDifferential z v / shearTailRadius z| ≤ 8192 * E * B := by
      rw [abs_div, abs_of_pos hR]
      calc
        _ ≤ (4096 * a * E * B) / (a / 2) := div_le_div₀ (by positivity [ha.1]) HDG (by positivity [ha.1]) HR.1
        _ = _ := by field_simp [ha.1.ne']; ring
    have H2 : |shearTailRadiusNumerator z * shearTailRadiusDifferential z v / shearTailRadius z ^ 2| ≤ 20480 * E * B := by
      rw [abs_div, abs_mul, abs_of_pos (sq_pos_of_pos hR)]
      calc
        _ ≤ ((128 * a ^ 2 * E) * (40 * B)) / (a / 2) ^ 2 := div_le_div₀
          (by positivity) (mul_le_mul HG HD (abs_nonneg _) (by positivity))
          (by positivity [ha.1]) (pow_le_pow_left₀ (by positivity [ha.1]) HR.1 2)
        _ = _ := by field_simp [ha.1.ne']; ring
    have H := abs_sub (shearTailRadiusNumeratorDifferential z v / shearTailRadius z)
      (shearTailRadiusNumerator z * shearTailRadiusDifferential z v / shearTailRadius z ^ 2)
    dsimp only [shearTailRadiusRateDifferential]
    nlinarith only [H, H1, H2, mul_nonneg hE hB]

end BianchiIX
