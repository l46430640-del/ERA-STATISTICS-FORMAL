import BianchiIX.Dynamics.EntranceRadiusCorrectionBounds
import BianchiIX.Dynamics.EntranceRadialReturnDifferential

noncomputable section

namespace BianchiIX

/-- A tangent vector to a constant active-wall section retains the two correction scales. -/
theorem exists_entranceRadiusCorrection_variation_bound :
    ∃ C > (0 : ℝ), ∀ (k : ℝ) (y : ProjectiveState), 7 / 4 ≤ k → entranceRegion k y → 0 < y 2 →
      ∀ ξ : ProjectiveState, ξ 2 = 0 →
      let b := y 1 + y 3
      |fderiv ℝ entranceRadiusCorrection y ξ| ≤ C *
        (b ^ 2 / k ^ 2 * |fderiv ℝ entranceStableRadius y ξ| + b / k * (|ξ 1| + |ξ 3|)) := by
  obtain ⟨C, hC, HC⟩ := exists_entranceRadiusCorrection_bounds
  refine ⟨C, hC, ?_⟩
  intro k y hk hy hv ξ hξ
  obtain ⟨Ψ, HΨ⟩ := exists_entranceRegion_radial_inverse hk hy hv
  obtain ⟨_, hr, hw⟩ := HC k y hk hy hv Ψ HΨ
  let z := entranceRadialCoordinates y
  let D := fderiv ℝ (fun z => entranceRadiusCorrection (Ψ z)) z
  let η := entranceRadialDifferential y ξ
  have hm : 2 ≤ y 0 := by linarith [(entranceRegion_phase hk hy).1]
  have hu : |y 1| < 1 / 200 := by rw [abs_of_nonneg hy.2.2.1.1]; linarith [hy.2.2.1.2]
  have hw' : |y 3| < 1 / 200 := by rw [abs_of_nonneg hy.2.2.2.2.1]; linarith [hy.2.2.2.2.2]
  have hc := (contDiffAt_entranceRadiusCorrection_two hm hu hw' hv).differentiableAt (by norm_num)
  have he : fderiv ℝ entranceRadiusCorrection y ξ = D η := by
    dsimp only [D, z, η]
    rw [HΨ.scalar_differential hc, (entranceRegion_radialDifferential_inverse hk hy hv).1]
  have hη : η = η 0 • Pi.single 0 1 + η 1 • Pi.single 1 1 + η 3 • Pi.single 3 1 := by
    ext i
    fin_cases i <;> simp [η, entranceRadialDifferential_apply, hξ]
  have hsum : D η = D (Pi.single 0 1) * η 0 + D (Pi.single 1 1) * η 1 + D (Pi.single 3 1) * η 3 := by
    conv_lhs => rw [hη]
    simp only [map_add, map_smul, smul_eq_mul]
    ring
  have hU : |D (Pi.single 1 1)| ≤ C * (y 1 + y 3) / k := by linarith only [hw, abs_nonneg (D (Pi.single 3 1))]
  have hW : |D (Pi.single 3 1)| ≤ C * (y 1 + y 3) / k := by linarith only [hw, abs_nonneg (D (Pi.single 1 1))]
  dsimp only
  rw [he, hsum]
  calc
    _ ≤ |D (Pi.single 0 1) * η 0| + |D (Pi.single 1 1) * η 1| + |D (Pi.single 3 1) * η 3| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ = |D (Pi.single 0 1)| * |η 0| + |D (Pi.single 1 1)| * |η 1| + |D (Pi.single 3 1)| * |η 3| := by
      simp only [abs_mul]
    _ ≤ (C * (y 1 + y 3) ^ 2 / k ^ 2) * |η 0| +
        (C * (y 1 + y 3) / k) * |η 1| + (C * (y 1 + y 3) / k) * |η 3| :=
      add_le_add (add_le_add (mul_le_mul_of_nonneg_right hr (abs_nonneg _))
        (mul_le_mul_of_nonneg_right hU (abs_nonneg _))) (mul_le_mul_of_nonneg_right hW (abs_nonneg _))
    _ = _ := by simp only [η, entranceRadialDifferential_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]; ring

end BianchiIX
