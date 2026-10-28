import BianchiIX.Algebra.ConnectionBounds
import BianchiIX.Algebra.CoreAngle

noncomputable section

namespace BianchiIX

theorem entrance_phase_bounds {k m v : ℝ} (hk : 7 / 4 ≤ k) (hm : 1 ≤ m)
    (hr : |coreRadius m v - k| ≤ k / 100) (hv : 0 ≤ v ∧ v ≤ 1) :
    4 / 5 * k ≤ m - 1 ∧ m - 1 ≤ 101 / 100 * k := by
  have hk0 : 0 ≤ k := by linarith
  have hR0 : 0 ≤ coreRadius m v := Real.sqrt_nonneg _
  obtain ⟨hRlo, hRhi⟩ := abs_le.mp hr
  have he := coreRadius_sq m v
  unfold coreEnergy at he
  have hv2 : v ^ 2 ≤ 1 := by nlinarith [mul_nonneg hv.1 (sub_nonneg.mpr hv.2)]
  have hR2 := mul_nonneg (show 0 ≤ coreRadius m v - 99 / 100 * k by linarith)
    (show 0 ≤ coreRadius m v + 99 / 100 * k by positivity)
  have hk2 := mul_nonneg (sub_nonneg.mpr hk) (show 0 ≤ k + 7 / 4 by linarith)
  constructor
  · by_contra h
    have h' : m - 1 < 4 / 5 * k := lt_of_not_ge h
    have hs := mul_nonneg (sub_nonneg.mpr h'.le) (show 0 ≤ 4 / 5 * k + (m - 1) by linarith)
    nlinarith only [he, hR2, hk2, hv2, hs]
  · have ht : m - 1 ≤ coreRadius m v := by
      nlinarith only [he, sq_nonneg v, hR0, hm]
    linarith only [ht, hRhi]

theorem entrance_speed_bounds {k m u v w : ℝ} (hk : 7 / 4 ≤ k)
    (hm : 4 / 5 * k ≤ m - 1 ∧ m - 1 ≤ 101 / 100 * k)
    (hu : 0 ≤ u ∧ u ≤ 1 / 10000) (hv : 0 ≤ v ∧ v ≤ 1)
    (hw : 0 ≤ w ∧ w ≤ 1 / 10000) :
    3 / 4 * k ≤ connectionSpeed m u v w ∧ connectionSpeed m u v w ≤ 21 / 20 * k := by
  have hC := connection_coupling_bounds hu.1 hv ⟨hw.1, by linarith [hw.2]⟩
  have hu2 : u ^ 2 ≤ (1 / 10000 : ℝ) ^ 2 := pow_le_pow_left₀ hu.1 hu.2 2
  unfold connectionSpeed
  constructor <;> nlinarith only [hm.1, hm.2, hC.1, hC.2, hu.2, hu2, hk]

theorem entrance_strong_clock_rate {k m u v w : ℝ} (hk : 7 / 4 ≤ k)
    (hm : 4 / 5 * k ≤ m - 1 ∧ m - 1 ≤ 101 / 100 * k)
    (hu : 0 ≤ u ∧ u ≤ 1 / 10000) (hv : 0 ≤ v ∧ v ≤ 1)
    (hw : 0 ≤ w ∧ w ≤ 1 / 10000) :
    connectionStrongRate m u v w / connectionSpeed m u v w ≤ -(1 + k / 3) := by
  have hD := entrance_speed_bounds hk hm hu hv hw
  have hD0 : 0 < connectionSpeed m u v w := by linarith [hD.1]
  have hC := (connection_coupling_bounds hu.1 hv ⟨hw.1, by linarith [hw.2]⟩).1
  have hmu : -(m + 1) * u ^ 2 ≤ (m + 1) * coupling u v w := by
    convert! mul_le_mul_of_nonneg_left hC (show 0 ≤ m + 1 by linarith [hm.1]) using 1
    ring
  have hcoef : m + 2 ≤ 4 * connectionSpeed m u v w := by linarith [hm.2, hD.1]
  have hmul := mul_le_mul_of_nonneg_right hcoef (sq_nonneg u)
  have hrem : (-(v - w) ^ 2 + u ^ 2 - (m + 1) * coupling u v w) /
      (2 * connectionSpeed m u v w) ≤ 2 * u ^ 2 := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * connectionSpeed m u v w)).mpr
    nlinarith only [hmu, hmul, sq_nonneg (v - w)]
  have hid := (connection_clock_identities hD0.ne').2
  have hu2 : u ^ 2 ≤ (1 / 10000 : ℝ) ^ 2 := pow_le_pow_left₀ hu.1 hu.2 2
  linarith only [hid, hrem, hu2, hm.1, hk]

theorem entrance_weak_clock_rate {k m u v w : ℝ} (hk : 7 / 4 ≤ k)
    (hm : 4 / 5 * k ≤ m - 1 ∧ m - 1 ≤ 101 / 100 * k)
    (hu : 0 ≤ u ∧ u ≤ 1 / 10000) (hv : 0 ≤ v ∧ v ≤ 1)
    (hw : 0 ≤ w ∧ w ≤ 1 / 10000) :
    (-m - 1 - coupling u v w) / connectionSpeed m u v w ≤ -(1 + 1 / k) := by
  have hk0 : 0 < k := by linarith
  have hD := entrance_speed_bounds hk hm hu hv hw
  have hD0 : 0 < connectionSpeed m u v w := by linarith [hD.1]
  have hC := (connection_coupling_bounds hu.1 hv ⟨hw.1, by linarith [hw.2]⟩).1
  have hu2 : u ^ 2 ≤ (1 / 10000 : ℝ) ^ 2 := pow_le_pow_left₀ hu.1 hu.2 2
  have hCu := mul_le_mul_of_nonneg_left hC hk0.le
  have hku := mul_le_mul_of_nonneg_left hu2 hk0.le
  have hfrac : 1 / k ≤ 2 * (1 + coupling u v w) / connectionSpeed m u v w := by
    apply (div_le_div_iff₀ hk0 hD0).mpr
    nlinarith only [hCu, hku, hD.2, hk0]
  have hid := (connection_clock_identities hD0.ne').1
  linarith only [hid, hfrac]

theorem entrance_denom_bounds {k m u v w : ℝ} (hk : 7 / 4 ≤ k)
    (hm : 4 / 5 * k ≤ m - 1 ∧ m - 1 ≤ 101 / 100 * k)
    (hu : 0 ≤ u ∧ u ≤ 1 / 10000) (hv : 0 ≤ v ∧ v ≤ 1)
    (hw : 0 ≤ w ∧ w ≤ 1 / 10000) :
    0 < projectiveDenom m u v w ∧ projectiveDenom m u v w ≤ 6 * (k + 1) ^ 2 := by
  have hpos := (connection_denom_bound (m := -m) hu hv ⟨hw.1, by linarith [hw.2]⟩).2
  simp only [neg_neg] at hpos
  refine ⟨hpos, ?_⟩
  have hu2 : u ^ 2 ≤ 1 := (pow_le_pow_left₀ hu.1 (show u ≤ 1 by linarith [hu.2]) 2).trans_eq (by norm_num)
  have hv2 : v ^ 2 ≤ 1 := (pow_le_pow_left₀ hv.1 hv.2 2).trans_eq (by norm_num)
  have hw2 : w ^ 2 ≤ 1 := (pow_le_pow_left₀ hw.1 (show w ≤ 1 by linarith [hw.2]) 2).trans_eq (by norm_num)
  have hm0 : 0 ≤ m := by linarith [hm.1]
  have hmsq := mul_nonneg (show 0 ≤ 2 * (k + 1) - m by linarith [hm.2])
    (show 0 ≤ 2 * (k + 1) + m by linarith)
  unfold projectiveDenom curvature
  nlinarith only [hmsq, hu2, hv2, hw2, mul_nonneg hu.1 hv.1, mul_nonneg hv.1 hw.1,
    mul_nonneg hw.1 hu.1, sq_nonneg (k - 1), hk]

end BianchiIX
