import BianchiIX.Dynamics.EntranceRadialVariation
import BianchiIX.Dynamics.EntranceDriftRefinedEstimates

noncomputable section

namespace BianchiIX

theorem continuousAt_entranceRadialInverseDifferential_apply {y : ProjectiveState} {k : ℝ}
    (hk : 7 / 4 ≤ k) (hy : entranceRegion k y) (hv : 0 < y 2) (v : ProjectiveState) :
    ContinuousAt (fun z => entranceRadialInverseDifferential z v) y := by
  have hm : 2 ≤ y 0 := by linarith [(entranceRegion_phase hk hy).1]
  have hu : |y 1| < 1 / 200 := by rw [abs_of_nonneg hy.2.2.1.1]; linarith [hy.2.2.1.2]
  have hw : |y 3| < 1 / 200 := by rw [abs_of_nonneg hy.2.2.2.2.1]; linarith [hy.2.2.2.2.2]
  have hP := (contDiffAt_entranceStablePhase_two hm hu hw).continuousAt
  have hR := (contDiffAt_entranceStableRadius_two hm hu hw hv).continuousAt
  have hpartial (i : Fin 4) := (contDiffAt_entranceStablePartial_one hm hu hw i).continuousAt
  have hbounds := entranceRegion_stable_radial_bounds hk hy
  have hchi : entranceStablePhase y - 1 ≠ 0 := by linarith [hbounds.1.1]
  have hPM : entranceStablePartial y 0 ≠ 0 := by linarith [hbounds.2.2.1]
  have hden := mul_ne_zero hchi hPM
  simp only [entranceRadialInverseDifferential_apply]
  apply continuousAt_pi.mpr
  intro i
  fin_cases i
  · exact ((((hR.div ((hP.sub_const 1).mul (hpartial 0)) hden).mul_const (v 0)).sub
      (((hpartial 1).div (hpartial 0) hPM).mul_const (v 1))).sub
      (((continuousAt_apply 2 y).div ((hP.sub_const 1).mul (hpartial 0)) hden).mul_const (v 2))).sub
      (((hpartial 3).div (hpartial 0) hPM).mul_const (v 3))
  all_goals exact continuousAt_const

theorem continuousAt_entranceRadialDriftDifferential_apply {y : ProjectiveState} {k : ℝ}
    (hk : 7 / 4 ≤ k) (hy : entranceRegion k y) (hv : 0 < y 2) (v : ProjectiveState) :
    ContinuousAt (fun z => entranceRadialDriftDifferential z v) y :=
  ((contDiffAt_entranceRadialDrift_one hk hy hv).continuousAt_fderiv (by norm_num)).clm_apply
    (continuousAt_entranceRadialInverseDifferential_apply hk hy hv v)

theorem continuousAt_entranceRadialVariationCoefficients {y : ProjectiveState} {k : ℝ}
    (hk : 7 / 4 ≤ k) (hy : entranceRegion k y) (hv : 0 < y 2) :
    ContinuousAt entranceRadialVariationCoefficients y := by
  apply continuousAt_pi.mpr
  intro i
  fin_cases i
  · exact continuousAt_entranceRadialDriftDifferential_apply hk hy hv (Pi.single 0 1)
  · exact (continuousAt_apply 1 y).mul (continuousAt_entranceRadialDriftDifferential_apply hk hy hv (Pi.single 1 1))
  · exact (continuousAt_apply 3 y).mul (continuousAt_entranceRadialDriftDifferential_apply hk hy hv (Pi.single 3 1))

theorem exists_entranceRadialVariationCoefficients_bounds :
    ∃ C > (0 : ℝ), ∀ (k : ℝ) (y : ProjectiveState), 7 / 4 ≤ k → entranceRegion k y → 0 < y 2 →
      |entranceRadialVariationCoefficients y 0| ≤ C * (y 1 * y 2 / k ^ 2 + y 2 ^ 2 * y 3 ^ 2 / k ^ 3) ∧
      |entranceRadialVariationCoefficients y 1| ≤ C * (y 1 * y 2) ∧
      |entranceRadialVariationCoefficients y 2| ≤ C * (y 1 * y 2 * y 3 + y 2 ^ 2 * y 3 ^ 2 / k ^ 2) := by
  obtain ⟨C, hC, HC⟩ := exists_entranceRadialDrift_basic_bounds
  refine ⟨C, hC, ?_⟩
  intro k y hk hy hv
  obtain ⟨Ψ, H⟩ := exists_entranceRegion_radial_inverse hk hy hv
  have hb := (HC k y hk hy hv Ψ H).2
  rw [H.radialDriftDifferential_eq hk hy hv] at hb
  exact hb

theorem exists_entranceRadialVariationCoefficients_refined_bounds :
    ∃ C > (0 : ℝ), ∀ (k : ℝ) (y : ProjectiveState), 7 / 4 ≤ k → entranceRegion k y →
      k * (y 1 + y 3) ^ 2 ≤ 1 → 0 < y 2 →
      |entranceRadialVariationCoefficients y 0| ≤ C * (y 1 * y 2 / k ^ 2 + y 2 ^ 2 * y 3 ^ 2 / k ^ 5) ∧
      |entranceRadialVariationCoefficients y 1| ≤ C * (y 1 * y 2) ∧
      |entranceRadialVariationCoefficients y 2| ≤ C * (y 1 * y 2 * y 3 + y 2 ^ 2 * y 3 ^ 2 / k ^ 4) := by
  obtain ⟨C, hC, HC⟩ := exists_entranceRadialDrift_refined_bounds
  refine ⟨C, hC, ?_⟩
  intro k y hk hy hsmall hv
  obtain ⟨Ψ, H⟩ := exists_entranceRegion_radial_inverse hk hy hv
  have hb := (HC k y hk hy hsmall hv Ψ H).2
  rw [H.radialDriftDifferential_eq hk hy hv] at hb
  exact hb

theorem exists_entranceRadialVariationCoefficients_weighted_bounds :
    ∃ C > (0 : ℝ), ∀ (k θ : ℝ) (y : ProjectiveState), 7 / 4 ≤ k → entranceRegion k y → 0 < y 2 →
      (θ = 1 ∨ (θ = 1 / k ^ 2 ∧ k * (y 1 + y 3) ^ 2 ≤ 1)) →
      |entranceRadialVariationCoefficients y 0| ≤ C * (y 1 * y 2 / k ^ 2 + θ * y 2 ^ 2 * y 3 ^ 2 / k ^ 3) ∧
      |entranceRadialVariationCoefficients y 1| ≤ C * (y 1 * y 2) ∧
      |entranceRadialVariationCoefficients y 2| ≤ C * (y 1 * y 2 * y 3 + θ * y 2 ^ 2 * y 3 ^ 2 / k ^ 2) := by
  obtain ⟨A, hA, HA⟩ := exists_entranceRadialVariationCoefficients_bounds
  obtain ⟨B, hB, HB⟩ := exists_entranceRadialVariationCoefficients_refined_bounds
  refine ⟨A + B, by positivity, ?_⟩
  intro k θ y hk hy hv hθ
  have hk0 : 0 < k := by linarith
  have hu0 := hy.2.2.1.1
  have hv0 := hv.le
  have hw0 := hy.2.2.2.2.1
  rcases hθ with rfl | ⟨rfl, hsmall⟩
  · simp only [one_mul]
    obtain ⟨hr, hx, hw⟩ := HA k y hk hy hv
    refine ⟨hr.trans ?_, hx.trans ?_, hw.trans ?_⟩
    all_goals exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hB.le) (by positivity)
  · have h3 : (1 / k ^ 2) * y 2 ^ 2 * y 3 ^ 2 / k ^ 3 = y 2 ^ 2 * y 3 ^ 2 / k ^ 5 := by
      field_simp
    have h2 : (1 / k ^ 2) * y 2 ^ 2 * y 3 ^ 2 / k ^ 2 = y 2 ^ 2 * y 3 ^ 2 / k ^ 4 := by
      field_simp
    rw [h3, h2]
    obtain ⟨hr, hx, hw⟩ := HB k y hk hy hsmall hv
    refine ⟨hr.trans ?_, hx.trans ?_, hw.trans ?_⟩
    all_goals exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hA.le) (by positivity)

end BianchiIX
