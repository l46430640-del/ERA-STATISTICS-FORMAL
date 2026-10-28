import BianchiIX.Dynamics.CoreWeightedVariation
import BianchiIX.Algebra.CoreBounds

noncomputable section

namespace BianchiIX

theorem coreBootstrap_diagonal_factors {k r u w : ℝ} (hk : 6 ≤ k)
    (hr : 99 / 100 * k ≤ r)
    (hu : 0 ≤ u ∧ u ≤ (1 / 10000) / k) (hw : 0 ≤ w ∧ w ≤ (1 / 10000) / k) :
    let d := coreClockFactor r u w
    99 / 100 ≤ (r ^ 2 + u ^ 2 - w ^ 2) / (r ^ 2 * d ^ 2) ∧
    99 / 100 ≤ (r ^ 2 - u ^ 2 + w ^ 2) / (r ^ 2 * d ^ 2) ∧
    u ^ 2 / (r * d) ≤ 1 / 100 := by
  let d := coreClockFactor r u w
  have hr5 : 5 ≤ r := by linarith
  have hr0 : 0 < r := by linarith
  have hr2 : 25 ≤ r ^ 2 := by nlinarith [sq_nonneg (r - 5)]
  obtain ⟨hdlo, hdhi⟩ := coreBootstrap_clock_bounds hk hr hu hw
  change 999 / 1000 ≤ d at hdlo
  change d ≤ 1 at hdhi
  have hd0 : 0 < d := by linarith
  have hu' := coreBootstrap_wall_bound hk hu.2
  have hw' := coreBootstrap_wall_bound hk hw.2
  have hu2 : u ^ 2 ≤ (1 / 60000 : ℝ) ^ 2 := (sq_le_sq₀ hu.1 (by norm_num)).mpr hu'
  have hw2 : w ^ 2 ≤ (1 / 60000 : ℝ) ^ 2 := (sq_le_sq₀ hw.1 (by norm_num)).mpr hw'
  have hd2 : d ^ 2 ≤ 1 := by nlinarith
  have hden : r ^ 2 * d ^ 2 ≤ r ^ 2 := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hd2 (sq_nonneg r)
  have hden0 : 0 < r ^ 2 * d ^ 2 := by positivity
  have hrd : 1 ≤ r * d := by nlinarith
  refine ⟨(le_div_iff₀ hden0).mpr ?_, (le_div_iff₀ hden0).mpr ?_,
    (div_le_iff₀ (mul_pos hr0 hd0)).mpr ?_⟩
  · nlinarith only [hden, hw2, hr2, sq_nonneg u]
  · nlinarith only [hden, hu2, hr2, sq_nonneg w]
  · nlinarith only [hu2, hrd]

/-- A negative numerator and the combined diagonal suffice; no upper bound on `|a|` is needed. -/
theorem coreBootstrap_strong_diagonal {k r u w a : ℝ} (hk : 6 ≤ k)
    (hr : 99 / 100 * k ≤ r)
    (hu : 0 ≤ u ∧ u ≤ (1 / 10000) / k) (hw : 0 ≤ w ∧ w ≤ (1 / 10000) / k)
    (ha : a ≤ -3 * k / 10) :
    a * (r ^ 2 + u ^ 2 - w ^ 2) / (r ^ 2 * coreClockFactor r u w ^ 2) +
      u ^ 2 / (r * coreClockFactor r u w) ≤ -k / 4 := by
  obtain ⟨hq, _, he⟩ := coreBootstrap_diagonal_factors hk hr hu hw
  have H := mul_le_mul_of_nonpos_left hq (show a ≤ 0 by linarith)
  rw [← mul_div_assoc] at H
  nlinarith

theorem coreBootstrap_weak_diagonal {k r u w c : ℝ} (hk : 6 ≤ k)
    (hr : 99 / 100 * k ≤ r ∧ r ≤ 101 / 100 * k)
    (hu : 0 ≤ u ∧ u ≤ (1 / 10000) / k) (hw : 0 ≤ w ∧ w ≤ (1 / 10000) / k)
    (hc : 0 ≤ c) :
    -2 * (1 + c) * (r ^ 2 - u ^ 2 + w ^ 2) / (r ^ 3 * coreClockFactor r u w ^ 2) -
      2 * u * w / (r * coreClockFactor r u w) ≤ -1 / k := by
  let d := coreClockFactor r u w
  have hr0 : 0 < r := by linarith [hr.1]
  have hk0 : 0 < k := by linarith
  have hd0 : 0 < d := by
    have H := (coreBootstrap_clock_bounds hk hr.1 hu hw).1
    change 999 / 1000 ≤ d at H
    linarith
  obtain ⟨_, hq, _⟩ := coreBootstrap_diagonal_factors hk hr.1 hu hw
  let q := (r ^ 2 - u ^ 2 + w ^ 2) / (r ^ 2 * d ^ 2)
  change 99 / 100 ≤ q at hq
  have hcq : 99 / 100 ≤ (1 + c) * q := by nlinarith
  have H := mul_le_mul_of_nonpos_left hcq
    (div_nonpos_of_nonpos_of_nonneg (by norm_num : (-2 : ℝ) ≤ 0) hr0.le)
  have hneg : -2 / r * (99 / 100) ≤ -1 / k := by
    calc
      -2 / r * (99 / 100) = (-198 / 100) / r := by ring
      _ ≤ -1 / k := (div_le_div_iff₀ hr0 hk0).mpr (by nlinarith [hr.2])
  have he := div_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hu.1) hw.1)
    (le_of_lt (mul_pos hr0 hd0))
  have hid : -2 * (1 + c) * (r ^ 2 - u ^ 2 + w ^ 2) / (r ^ 3 * d ^ 2) =
      (-2 / r) * ((1 + c) * q) := by dsimp [q]; ring
  change _ - 2 * u * w / (r * d) ≤ -1 / k
  rw [hid]
  linarith

theorem coreWeightedJacobian_strong_bound {k z : ℝ} {y : CoreAngleState}
    (hk : 6 ≤ k) (hr : 99 / 100 * k ≤ y 0)
    (hu : 0 ≤ y 1 ∧ y 1 ≤ (1 / 10000) / k)
    (hw : 0 ≤ y 2 / (y 0 / Real.cosh z) ∧ y 2 / (y 0 / Real.cosh z) ≤ (1 / 10000) / k) :
    (coreWeightedJacobian k z y) 1 1 ≤ -k / 4 := by
  have hr0 : 0 < y 0 := by linarith
  have hd : (coreAuxiliary z y) 1 ≠ 0 := by
    have H := (coreBootstrap_clock_bounds hk hr hu hw).1
    change 999 / 1000 ≤ (coreAuxiliary z y) 1 at H
    linarith
  have hv : y 0 / Real.cosh z ≤ y 0 := div_le_self hr0.le (Real.one_le_cosh z)
  have hc : -1 ≤ -Real.tanh z := by linarith [Real.tanh_lt_one z]
  have ha : (coreAuxiliary z y) 2 ≤ -3 * k / 10 := by
    have H := coreBootstrap_strong_numerator hk hr hv hc hu hw
    convert! H using 1
    dsimp [coreAuxiliary]
    field_simp [ne_of_gt hr0]
    ring
  rw [coreWeightedJacobian_strong_diagonal k z (ne_of_gt hr0) hd]
  exact coreBootstrap_strong_diagonal hk hr hu hw ha

theorem coreWeightedJacobian_weak_bound {k z : ℝ} {y : CoreAngleState}
    (hk : 6 ≤ k) (hr : 99 / 100 * k ≤ y 0 ∧ y 0 ≤ 101 / 100 * k)
    (hv : 1 ≤ y 0 / Real.cosh z)
    (hu : 0 ≤ y 1 ∧ y 1 ≤ (1 / 10000) / k)
    (hw : 0 ≤ y 2 / (y 0 / Real.cosh z) ∧ y 2 / (y 0 / Real.cosh z) ≤ (1 / 10000) / k) :
    (coreWeightedJacobian k z y) 2 2 ≤ -1 / k := by
  have hr0 : 0 < y 0 := by linarith [hr.1]
  have hd : (coreAuxiliary z y) 1 ≠ 0 := by
    have H := (coreBootstrap_clock_bounds hk hr.1 hu hw).1
    change 999 / 1000 ≤ (coreAuxiliary z y) 1 at H
    linarith
  have hc : 0 ≤ (coreAuxiliary z y) 0 := coreBootstrap_coupling_nonneg hk hv hu hw.1
  rw [coreWeightedJacobian_weak_diagonal k z (ne_of_gt hr0) hd]
  exact coreBootstrap_weak_diagonal hk hr hu hw hc

end BianchiIX
