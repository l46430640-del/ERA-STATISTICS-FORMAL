import BianchiIX.Dynamics.CoreLogRateVariation

noncomputable section

namespace BianchiIX

/-- The angular field at an arbitrary interior entrance retains both small wall amplitudes. -/
theorem partialCore_field_bounds {k : ℝ} {y : ProjectiveState}
    (hk : 6 ≤ k) (hy : coreRegion k y) (hR : coreRadius (y 0) (y 2) = k) :
    let F := coreAngleField (projectiveCoreAngle y) (toCoreAngleState y)
    let p := y 2 * y 3
    |F 0| ≤ 2 * (k * y 1 + p ^ 2 / k) ∧
      |F 1| ≤ 2 * k * y 1 ∧ |F 2| ≤ 4 * p / k := by
  intro F p
  have hk0 : 0 < k := by linarith only [hk]
  have hv : 0 < y 2 := lt_of_lt_of_le zero_lt_one hy.2.1
  obtain ⟨hu, hw⟩ := coreRegion_wall_bounds hy
  have hp : 0 ≤ p := hy.2.2.2.1
  have hvk : y 2 ≤ k := by
    simpa only [hR, abs_of_pos hv] using (coreRadius_component_bounds (y 0) (y 2)).2
  have hwp : y 3 ≤ p := by
    dsimp [p]
    nlinarith only [mul_le_mul_of_nonneg_right hy.2.1 hw.1]
  have hw2 : y 3 ^ 2 / k ≤ p ^ 2 / k :=
    div_le_div_of_nonneg_right ((sq_le_sq₀ hw.1 hp).mpr hwp) hk0.le
  have huv : y 1 * y 2 ≤ k * y 1 := by
    nlinarith only [mul_le_mul_of_nonneg_left hvk hu.1]
  have huw : y 1 * y 3 ≤ y 1 / 60000 := by
    nlinarith only [mul_le_mul_of_nonneg_left (coreBootstrap_wall_bound hk hw.2) hu.1]
  have huu : y 1 ^ 2 / k ≤ y 1 / 60000 :=
    (div_le_self (sq_nonneg _) (by linarith only [hk])).trans (by
      nlinarith only [mul_le_mul_of_nonneg_left (coreBootstrap_wall_bound hk hu.2) hu.1])
  obtain ⟨hU, hP, _⟩ := coreRegion_log_rate_bounds hk hy
  have hcoef := coreAngleField_log_rates (projectiveCoreAngle y) (toCoreAngleState y)
  refine ⟨?_, ?_, ?_⟩
  · have H := core_radial_velocity_bound hk
      (r := k) (by linarith only [hk]) hy.2.1 hu hw
      (Real.abs_tanh_lt_one (projectiveCoreAngle y)).le
    have hid := coreAngleField_radius_projective hv
    rw [hR] at hid
    change F 0 = _ at hid
    rw [hid]
    apply H.trans
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 999 / 1000)).mpr
    have hku : 6 * y 1 ≤ k * y 1 := mul_le_mul_of_nonneg_right hk hu.1
    have hp2 : 0 ≤ p ^ 2 / k := div_nonneg (sq_nonneg _) hk0.le
    linarith only [huv, huw, huu, hw2, hku, hu.1, hp2]
  · change |coreAngleField (projectiveCoreAngle y) (toCoreAngleState y) 1| ≤ _
    rw [hcoef.1, abs_mul]
    change |y 1| * _ ≤ _
    rw [abs_of_nonneg hu.1]
    have H := mul_le_mul_of_nonneg_right hU hu.1
    convert! H using 1
    ring
  · change |coreAngleField (projectiveCoreAngle y) (toCoreAngleState y) 2| ≤ _
    rw [hcoef.2, abs_mul]
    change |p| * _ ≤ _
    rw [abs_of_nonneg hp]
    have H := mul_le_mul_of_nonneg_right hP hp
    convert! H using 1 <;> ring

theorem partialCore_weighted_field_bound {k : ℝ} {y : ProjectiveState}
    (hk : 6 ≤ k) (hy : coreRegion k y) (hR : coreRadius (y 0) (y 2) = k) :
    ‖scaleCoreVariation k (coreAngleField (projectiveCoreAngle y) (toCoreAngleState y))‖ ≤
      4 * (k ^ 2 * y 1 + (y 2 * y 3) / k) := by
  let F := coreAngleField (projectiveCoreAngle y) (toCoreAngleState y)
  let p := y 2 * y 3
  have hk0 : 0 < k := by linarith only [hk]
  have hu : 0 ≤ y 1 := hy.2.2.1.1
  have hp : 0 ≤ p := hy.2.2.2.1
  have hp1 : p ≤ 1 := (coreBootstrap_wall_bound hk hy.2.2.2.2).trans (by norm_num)
  have hp2 : p ^ 2 / k ≤ p / k := div_le_div_of_nonneg_right (by nlinarith only [hp, hp1]) hk0.le
  have hku : k * y 1 ≤ k ^ 2 * y 1 := by
    have H : k ≤ k ^ 2 := by nlinarith only [hk]
    exact mul_le_mul_of_nonneg_right H hu
  obtain ⟨hR', hU, hP⟩ := partialCore_field_bounds hk hy hR
  change |F 0| ≤ 2 * (k * y 1 + p ^ 2 / k) at hR'
  change |F 1| ≤ 2 * k * y 1 at hU
  change |F 2| ≤ 4 * p / k at hP
  rw [show 4 * p / k = 4 * (p / k) by ring] at hP
  have hpdiv : 0 ≤ p / k := div_nonneg hp hk0.le
  have hkusq : 0 ≤ k ^ 2 * y 1 := mul_nonneg (sq_nonneg _) hu
  apply (pi_norm_le_iff_of_nonempty _).mpr
  intro i
  fin_cases i
  · change |F 0| ≤ _
    linarith only [hR', hp2, hku, hkusq, hpdiv]
  · change |k * F 1| ≤ _
    rw [abs_mul, abs_of_pos hk0]
    nlinarith only [mul_le_mul_of_nonneg_left hU hk0.le, hkusq, hpdiv]
  · change |F 2| ≤ _
    linarith only [hP, hkusq]

end BianchiIX
