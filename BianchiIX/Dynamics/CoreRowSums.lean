import BianchiIX.Dynamics.CoreWallCoefficients
import BianchiIX.Dynamics.CoreEntry

noncomputable section

namespace BianchiIX

/-- Signed row sums, with the diagonal damping retained. -/
theorem coreWeightedJacobian_row_sums {k z : ℝ} {y : CoreAngleState}
    (hk : 6 ≤ k) (hr : 99 / 100 * k ≤ y 0 ∧ y 0 ≤ 101 / 100 * k)
    (hv : 1 ≤ y 0 / Real.cosh z)
    (hu : 0 ≤ y 1 ∧ y 1 ≤ (1 / 10000) / k)
    (hw : 0 ≤ y 2 / (y 0 / Real.cosh z) ∧ y 2 / (y 0 / Real.cosh z) ≤ (1 / 10000) / k)
    (hp : y 2 ≤ (1 / 10000) / k) :
    let b := coreWeightedJacobian k z y
    b 0 0 + |b 0 1| + |b 0 2| ≤ 2 / Real.cosh z + 24 * ((1 / 10000) / k) ∧
    |b 1 0| + b 1 1 + |b 1 2| ≤ 0 ∧
    |b 2 0| + |b 2 1| + b 2 2 ≤ 0 := by
  let b := coreWeightedJacobian k z y
  let m := (1 / 10000) / k
  let v := y 0 / Real.cosh z
  have hk0 : 0 < k := by linarith
  have hv0 : 0 < v := by dsimp [v]; linarith
  have hm0 : 0 ≤ m := by dsimp [m]; positivity
  obtain ⟨h00, h01, h02⟩ := coreWeightedJacobian_radius_bounds hk hr hv hu hw
  change |b 0 0| ≤ 8 * m at h00
  change |b 0 1 + v / k| ≤ 8 * m / k at h01
  change |b 0 2| ≤ 8 * m / v at h02
  obtain ⟨h10, h12⟩ := coreWeightedJacobian_strong_off_diagonal hk hr hv hu hw
  obtain ⟨h20, h21⟩ := coreWeightedJacobian_weak_off_diagonal hk hr hv hu hw
  have h11 := coreWeightedJacobian_strong_bound hk hr.1 hu hw
  have h22 := coreWeightedJacobian_weak_bound hk hr hv hu hw
  constructor
  · have hmain : v / k ≤ 2 / Real.cosh z := by
      calc
        v / k = (y 0 / k) / Real.cosh z := by dsimp [v]; ring
        _ ≤ 2 / Real.cosh z := div_le_div_of_nonneg_right
          ((div_le_iff₀ hk0).mpr (by linarith only [hr.2, hk])) (Real.cosh_pos z).le
    have hrem1 : 8 * m / k ≤ 8 * m := div_le_self (by positivity) (by linarith)
    have hrem2 : 8 * m / v ≤ 8 * m := div_le_self (by positivity) hv
    have h01' : |b 0 1| ≤ |b 0 1 + v / k| + v / k := by
      have H := abs_sub (b 0 1 + v / k) (v / k)
      simpa only [add_sub_cancel_right, abs_of_nonneg (div_nonneg hv0.le hk0.le)] using H
    change b 0 0 + |b 0 1| + |b 0 2| ≤ 2 / Real.cosh z + 24 * m
    linarith only [h00, h01, h02, hmain, hrem1, hrem2, h01', le_abs_self (b 0 0)]
  constructor
  · have hu' := coreBootstrap_wall_bound hk hu.2
    have H : 2 * k * y 1 + 4 * y 1 ≤ k / 4 := by
      nlinarith only [hk, hu', mul_nonneg hk0.le (sub_nonneg.mpr hu')]
    linarith only [h10, h11, h12, H]
  · have hp0 : 0 ≤ y 2 := by
      have H := (le_div_iff₀ hv0).mp hw.1
      simpa only [zero_mul] using H
    have hp' := coreBootstrap_wall_bound hk hp
    have hpart : 8 * y 2 / k ≤ 8 * y 2 := div_le_self (by positivity) (by linarith)
    have H : 8 * y 2 / k ^ 2 + 8 * y 2 / k ≤ 1 / k := by
      calc
        _ = (8 * y 2 / k + 8 * y 2) / k := by ring
        _ ≤ 1 / k := div_le_div_of_nonneg_right (by linarith only [hpart, hp']) hk0.le
    have hneg : (-1 : ℝ) / k = -(1 / k) := by ring
    rw [hneg] at h22
    linarith only [h20, h21, h22, H]

theorem coreRegion_variational_row_sums {k : ℝ} {y : ProjectiveState}
    (hk : 6 ≤ k) (hy : coreRegion k y) :
    let z := coreAngle (y 0) (y 2)
    let b := coreWeightedJacobian k z (toCoreAngleState y)
    b 0 0 + |b 0 1| + |b 0 2| ≤ 2 / Real.cosh z + 24 * ((1 / 10000) / k) ∧
    |b 1 0| + b 1 1 + |b 1 2| ≤ 0 ∧
    |b 2 0| + |b 2 1| + b 2 2 ≤ 0 := by
  have hv0 : 0 < y 2 := lt_of_lt_of_le zero_lt_one hy.2.1
  have hcoord := (coreAngle_coordinates (m := y 0) hv0).1
  refine coreWeightedJacobian_row_sums hk (coreRegion_radius_bounds hk hy) ?_
    hy.2.2.1 ?_ hy.2.2.2.2
  · change 1 ≤ coreRadius (y 0) (y 2) / Real.cosh (coreAngle (y 0) (y 2))
    rw [hcoord]
    exact hy.2.1
  · change 0 ≤ y 2 * y 3 / (coreRadius (y 0) (y 2) / Real.cosh (coreAngle (y 0) (y 2))) ∧
      y 2 * y 3 / (coreRadius (y 0) (y 2) / Real.cosh (coreAngle (y 0) (y 2))) ≤ (1 / 10000) / k
    rw [hcoord, mul_div_cancel_left₀ _ (ne_of_gt hv0)]
    exact (coreRegion_wall_bounds hy).2

end BianchiIX
