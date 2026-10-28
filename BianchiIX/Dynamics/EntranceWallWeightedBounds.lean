import BianchiIX.Dynamics.EntranceWeakLogBounds

noncomputable section

namespace BianchiIX

/-- The weight is fixed at the reference entrance parameter, not differentiated. -/
theorem entranceWallLogRates_weighted_differential {y : ProjectiveState}
    (Ψ : ProjectiveState → ProjectiveState) {k : ℝ} (hk : k ≠ 0) (Z X Y : ℝ) :
    let z := entranceRadialCoordinates y
    let A := fderiv ℝ (fun z => entranceStrongLogRate (Ψ z)) z
    let B := fderiv ℝ (fun z => entranceWeakLogRate (Ψ z)) z
    let v : ProjectiveState := ![Z, y 1 * X, 0, y 3 * Y / k ^ 2]
    A v = A (Pi.single 0 1) * Z + (y 1 * A (Pi.single 1 1)) * X +
        (y 3 / k ^ 2 * A (Pi.single 3 1)) * Y ∧
      k ^ 2 * B v = (k ^ 2 * B (Pi.single 0 1)) * Z +
        (k ^ 2 * y 1 * B (Pi.single 1 1)) * X + (y 3 * B (Pi.single 3 1)) * Y := by
  have he : (![Z, y 1 * X, 0, y 3 * Y / k ^ 2] : ProjectiveState) =
      Z • Pi.single 0 1 + (y 1 * X) • Pi.single 1 1 + (y 3 * Y / k ^ 2) • Pi.single 3 1 := by
    ext i
    fin_cases i <;> simp
  dsimp only
  rw [he]
  simp only [map_add, map_smul, smul_eq_mul]
  constructor
  · ring
  · field_simp

/-- Pointwise coefficients for the weighted transverse variational equation on the full entrance region. -/
theorem exists_entranceWallLogRates_weighted_bounds :
    ∃ C > (0 : ℝ), ∀ (k : ℝ) (y : ProjectiveState), 7 / 4 ≤ k → entranceRegion k y → 0 < y 2 →
      ∀ Ψ : ProjectiveState → ProjectiveState, EntranceRadialInverseAt y Ψ →
        let z := entranceRadialCoordinates y
        let A := fderiv ℝ (fun z => entranceStrongLogRate (Ψ z)) z
        let B := fderiv ℝ (fun z => entranceWeakLogRate (Ψ z)) z
        |A (Pi.single 0 1)| + k ^ 2 * |B (Pi.single 0 1)| ≤ C ∧
          |y 1 * A (Pi.single 1 1)| ≤ C * y 1 ∧
          |y 3 / k ^ 2 * A (Pi.single 3 1)| ≤ C * y 3 / k ^ 2 ∧
          |k ^ 2 * y 1 * B (Pi.single 1 1)| ≤ C * k * y 1 * (y 2 + y 1 + y 3) ∧
          |y 3 * B (Pi.single 3 1)| ≤ C * (y 1 * y 3 / k + y 3 * (y 1 + y 3) / k ^ 3) := by
  obtain ⟨S, hS, HS⟩ := exists_entranceStrongLogRate_radial_bound
  obtain ⟨T, hT, HT⟩ := exists_entranceWeakLogRate_radial_bounds
  refine ⟨S + T + 200, by positivity, ?_⟩
  intro k y hk hy hv Ψ H
  have hk1 : 1 ≤ k := by linarith
  have hk0 : 0 < k := by linarith
  have hu := hy.2.2.1.1
  have hw := hy.2.2.2.2.1
  have hq : 0 ≤ y 2 + y 1 + y 3 := by positivity
  have hbq : y 1 + y 3 ≤ y 2 + y 1 + y 3 := by linarith
  have hS' (i : Fin 4) : |fderiv ℝ (fun z => entranceStrongLogRate (Ψ z))
      (entranceRadialCoordinates y) (Pi.single i 1)| ≤ S := by
    simpa only [Pi.norm_single, norm_one, mul_one] using HS k y hk hy hv Ψ H (Pi.single i 1)
  obtain ⟨hr, hU, hW⟩ := HT k y hk hy hv Ψ H
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have he : k ^ 2 * (128 / k ^ 2) = (128 : ℝ) := by field_simp
    have hb := mul_le_mul_of_nonneg_left hr (sq_nonneg k)
    rw [he] at hb
    linarith only [hb, hS' 0, hT]
  · rw [abs_mul, abs_of_nonneg hu]
    exact (mul_le_mul_of_nonneg_left (hS' 1) hu).trans (by nlinarith only [mul_nonneg hu hT.le, hu])
  · rw [abs_mul, abs_of_nonneg (div_nonneg hw (sq_nonneg k))]
    calc
      _ ≤ (y 3 / k ^ 2) * S := mul_le_mul_of_nonneg_left (hS' 3) (by positivity)
      _ ≤ (S + T + 200) * y 3 / k ^ 2 := by
        rw [div_mul_eq_mul_div]
        apply (div_le_div_iff_of_pos_right (sq_pos_of_pos hk0)).mpr
        nlinarith only [mul_nonneg hw hT.le, hw]
  · rw [abs_mul, abs_of_nonneg (mul_nonneg (sq_nonneg k) hu)]
    have hb : (y 1 + y 3) / k ≤ k * (y 2 + y 1 + y 3) := by
      apply (div_le_iff₀ hk0).mpr
      nlinarith only [hbq, mul_le_mul_of_nonneg_right (one_le_pow₀ hk1 (n := 2)) hq]
    calc
      _ ≤ (k ^ 2 * y 1) * (T * (y 1 + y 3) / k ^ 3 + 48 * (y 2 + y 1 + y 3) / k) :=
        mul_le_mul_of_nonneg_left hU (by positivity)
      _ = y 1 * (T * ((y 1 + y 3) / k) + 48 * (k * (y 2 + y 1 + y 3))) := by field_simp
      _ ≤ y 1 * (T * (k * (y 2 + y 1 + y 3)) + 48 * (k * (y 2 + y 1 + y 3))) :=
        mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left hb hT.le) le_rfl) hu
      _ ≤ _ := by nlinarith only [mul_nonneg hS.le (mul_nonneg (mul_nonneg hk0.le hu) hq),
        mul_nonneg (mul_nonneg hk0.le hu) hq]
  · rw [abs_mul, abs_of_nonneg hw]
    calc
      _ ≤ y 3 * (T * (y 1 + y 3) / k ^ 3 + 24 * y 1 / k) := mul_le_mul_of_nonneg_left hW hw
      _ = T * (y 3 * (y 1 + y 3) / k ^ 3) + 24 * (y 1 * y 3 / k) := by ring
      _ ≤ _ := by
        have hp : 0 ≤ y 3 * (y 1 + y 3) / k ^ 3 := by positivity
        have hq' : 0 ≤ y 1 * y 3 / k := by positivity
        nlinarith only [mul_nonneg hS.le hp, mul_nonneg hS.le hq', mul_nonneg hT.le hq', hp, hq']

end BianchiIX
