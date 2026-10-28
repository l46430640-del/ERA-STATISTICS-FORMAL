import BianchiIX.Dynamics.EntranceWallLogBounds

noncomputable section

namespace BianchiIX

private theorem weak_log_quotient_bound {k D c m a t A T : ℝ}
    (hk : 0 < k) (hD : k / 2 ≤ D) (hc : |c| ≤ 2) (hm : |m| ≤ 3 * k)
    (ha : |a| ≤ A) (ht : |t| ≤ T) :
    |(2 * c * a - 2 * m * t) / D ^ 2| ≤ 16 * A / k ^ 2 + 24 * T / k := by
  have hA := (abs_nonneg a).trans ha
  have hT := (abs_nonneg t).trans ht
  have hD0 : 0 < D := by linarith
  have hDsq : k ^ 2 / 4 ≤ D ^ 2 := by nlinarith only [hD, sq_nonneg (D - k / 2), hk]
  have hnum : |2 * c * a - 2 * m * t| ≤ 4 * A + 6 * k * T := by
    calc
      _ ≤ |2 * c * a| + |2 * m * t| := abs_sub _ _
      _ ≤ (2 * 2) * A + (2 * (3 * k)) * T := by
        simp only [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        exact add_le_add (mul_le_mul (mul_le_mul_of_nonneg_left hc (by norm_num)) ha (abs_nonneg _) (by norm_num))
          (mul_le_mul (mul_le_mul_of_nonneg_left hm (by norm_num)) ht (abs_nonneg _) (by positivity))
      _ = _ := by ring
  rw [abs_div, abs_of_nonneg (sq_nonneg D)]
  calc
    _ ≤ (4 * A + 6 * k * T) / (k ^ 2 / 4) := div_le_div₀ (by positivity) hnum (by positivity) hDsq
    _ = _ := by field_simp; ring

/-- The weak radial column has two powers of the entrance parameter in the denominator. -/
theorem exists_entranceWeakLogRate_radial_bounds :
    ∃ C > (0 : ℝ), ∀ (k : ℝ) (y : ProjectiveState), 7 / 4 ≤ k → entranceRegion k y → 0 < y 2 →
      ∀ Ψ : ProjectiveState → ProjectiveState, EntranceRadialInverseAt y Ψ →
        let L := fderiv ℝ (fun z => entranceWeakLogRate (Ψ z)) (entranceRadialCoordinates y)
        |L (Pi.single 0 1)| ≤ 128 / k ^ 2 ∧
          |L (Pi.single 1 1)| ≤ C * (y 1 + y 3) / k ^ 3 + 48 * (y 2 + y 1 + y 3) / k ∧
          |L (Pi.single 3 1)| ≤ C * (y 1 + y 3) / k ^ 3 + 24 * y 1 / k := by
  obtain ⟨J, hJ, HJ⟩ := exists_entranceRadialInverse_column_bounds
  refine ⟨16 * J, by positivity, ?_⟩
  intro k y hk hy hv Ψ H
  have hk0 : 0 < k := by linarith
  have hD : k / 2 ≤ entranceClockRate y := by linarith [(entranceRegion_speed hk hy).1]
  have hc := (entranceWallLogRates_base_bounds hk hy).1
  have hm : |y 0| ≤ 3 * k := by
    rw [abs_of_nonneg (by linarith [hy.1] : 0 ≤ y 0)]
    linarith [(entranceRegion_phase hk hy).2]
  obtain ⟨hr, hu, _, hw⟩ := HJ k y hk hy hv Ψ H
  have hr' : |fderiv ℝ Ψ (entranceRadialCoordinates y) (Pi.single 0 1) 0| ≤ 8 :=
    abs_le.mpr ⟨by linarith only [hr.1], hr.2⟩
  have ht : |y 2 + y 3 - 2 * y 1| ≤ 2 * (y 2 + y 1 + y 3) :=
    abs_le.mpr ⟨by linarith [hy.2.2.2.1.1, hy.2.2.2.2.1], by linarith [hy.2.2.1.1, hy.2.2.2.1.1, hy.2.2.2.2.1]⟩
  have hzero : |(0 : ℝ)| ≤ 0 := by norm_num
  obtain ⟨er, eu, ew⟩ := H.weakLogRate_partials hk hy
  dsimp only
  rw [er, eu, ew]
  refine ⟨?_, ?_, ?_⟩
  · have hb := weak_log_quotient_bound hk0 hD hc hm hr' hzero
    norm_num at hb
    exact hb
  · convert! weak_log_quotient_bound hk0 hD hc hm hu ht using 1
    field_simp
    ring
  · convert! weak_log_quotient_bound hk0 hD hc hm hw (le_of_eq (abs_of_nonneg hy.2.2.1.1)) using 1
    field_simp

end BianchiIX
