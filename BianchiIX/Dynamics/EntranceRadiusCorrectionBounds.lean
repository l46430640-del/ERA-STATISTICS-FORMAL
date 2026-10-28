import BianchiIX.Dynamics.EntranceRadiusCorrection
import BianchiIX.Dynamics.EntranceProjectionEstimates
import BianchiIX.Algebra.RadialComparison

noncomputable section

namespace BianchiIX

/-- The endpoint correction bounds hold throughout the entrance region, including the arrival section. -/
theorem exists_entranceRadiusCorrection_bounds :
    ∃ C > (0 : ℝ), ∀ (k : ℝ) (y : ProjectiveState), 7 / 4 ≤ k → entranceRegion k y → 0 < y 2 →
      ∀ Ψ : ProjectiveState → ProjectiveState, EntranceRadialInverseAt y Ψ →
      let b := y 1 + y 3
      let D := fderiv ℝ (fun z => entranceRadiusCorrection (Ψ z)) (entranceRadialCoordinates y)
      |entranceRadiusCorrection y| ≤ C * b ^ 2 / k ∧
      |D (Pi.single 0 1)| ≤ C * b ^ 2 / k ^ 2 ∧
      |D (Pi.single 1 1)| + |D (Pi.single 3 1)| ≤ C * b / k := by
  obtain ⟨C, hC, HC⟩ := exists_entranceProjection_estimates
  refine ⟨10 * C, by positivity, ?_⟩
  intro k y hk hy hv Ψ H
  let b := y 1 + y 3
  let q := y 0 - 1
  let χ := entranceStablePhase y - 1
  let R := coreRadius (y 0) (y 2)
  let r := entranceStableRadius y
  have hk0 : 0 < k := by linarith
  have hb : 0 ≤ b := add_nonneg hy.2.2.1.1 hy.2.2.2.2.1
  have hq0 : 0 < q := by dsimp [q]; linarith [(entranceRegion_phase hk hy).1]
  obtain ⟨hχ, _, hp⟩ := entranceRegion_stable_radial_bounds hk hy
  have hχ0 : 0 < χ := by dsimp [χ]; linarith [hχ.1]
  have hR0 : 0 < R := coreRadius_pos hv
  have hqR : q ≤ R := phaseNorm_ge hq0.le
  have hnorm : |r - R| ≤ |χ - q| := phaseNorm_sub_le hχ0 hq0
  have hphase : χ - q = entranceStablePhase y - y 0 := by dsimp [χ, q]; ring
  rw [hphase] at hnorm
  obtain ⟨hval, hpM, hpU, hpW, _⟩ := HC k y hk hy
  have hval' : |r - R| ≤ C * b ^ 2 / k := hnorm.trans hval
  have hphase' : |q - χ| ≤ C * b ^ 2 / k := by rw [abs_sub_comm, hphase]; exact hval
  have hrad := radial_correction_derivative_bound hk0 hq0.le hR0 hqR hχ.1
    (show 0 ≤ C * b ^ 2 / k by positivity) hval' hphase' hp.1 hpM
  have hwall := add_le_add
    (radial_wall_correction_bound (a := entranceStablePartial y 1) hq0.le hR0 hqR hp.1)
    (radial_wall_correction_bound (a := entranceStablePartial y 3) hq0.le hR0 hqR hp.1)
  have hm : 2 ≤ y 0 := by linarith [(entranceRegion_phase hk hy).1]
  have hu : |y 1| < 1 / 200 := by rw [abs_of_nonneg hy.2.2.1.1]; linarith [hy.2.2.1.2]
  have hw : |y 3| < 1 / 200 := by rw [abs_of_nonneg hy.2.2.2.2.1]; linarith [hy.2.2.2.2.2]
  obtain ⟨hr, hu', hw'⟩ := H.correction_partials hm hu hw hv
  dsimp only
  rw [hr, hu', hw']
  refine ⟨hval'.trans ?_, hrad.trans_eq ?_, hwall.trans ?_⟩
  · exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith : C ≤ 10 * C) (sq_nonneg b)) hk0.le
  · dsimp [b]
    ring
  · have hsum := add_le_add (mul_le_mul_of_nonneg_left hpU (by norm_num : (0 : ℝ) ≤ 2))
      (mul_le_mul_of_nonneg_left hpW (by norm_num : (0 : ℝ) ≤ 2))
    have hnonneg : 0 ≤ C * b / k := by positivity
    apply hsum.trans
    calc
      _ = 4 * (C * b / k) := by dsimp [b]; ring
      _ ≤ 10 * (C * b / k) := mul_le_mul_of_nonneg_right (by norm_num) hnonneg
      _ = _ := by dsimp [b]; ring

end BianchiIX
