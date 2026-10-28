import BianchiIX.Algebra.CoreAngle

noncomputable section

namespace BianchiIX

theorem coreBootstrap_radius {k r : ℝ} (hk : 6 ≤ k) (hr : 0 ≤ r)
    (he : |r ^ 2 - k ^ 2| < 1 / 8) : 99 / 100 * k ≤ r ∧ r ≤ 101 / 100 * k := by
  obtain ⟨hl, hu⟩ := abs_lt.mp he
  constructor
  · by_contra! hlt
    have hs : r ^ 2 < (99 / 100 * k) ^ 2 :=
      (sq_lt_sq₀ hr (by linarith)).mpr hlt
    nlinarith
  · by_contra! hgt
    have hs : (101 / 100 * k) ^ 2 < r ^ 2 :=
      (sq_lt_sq₀ (by linarith) hr).mpr hgt
    nlinarith

theorem coreBootstrap_wall_bound {k u : ℝ} (hk : 6 ≤ k) (hu : u ≤ (1 / 10000) / k) :
    u ≤ 1 / 60000 := by
  have hk0 : 0 < k := by linarith
  exact hu.trans ((div_le_iff₀ hk0).mpr (by linarith))

theorem coreBootstrap_clock_bounds {k r u w : ℝ} (hk : 6 ≤ k)
    (hr : 99 / 100 * k ≤ r)
    (hu : 0 ≤ u ∧ u ≤ (1 / 10000) / k) (hw : 0 ≤ w ∧ w ≤ (1 / 10000) / k) :
    999 / 1000 ≤ coreClockFactor r u w ∧ coreClockFactor r u w ≤ 1 := by
  have hr0 : 0 < r := by linarith
  have hu' := coreBootstrap_wall_bound hk hu.2
  have hw' := coreBootstrap_wall_bound hk hw.2
  have hdelta : (u - w) ^ 2 ≤ (1 / 60000 : ℝ) ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ 1 / 60000 - (u - w) by linarith)
      (show 0 ≤ 1 / 60000 + (u - w) by linarith)]
  have hsmall : (u - w) ^ 2 / r ^ 2 ≤ 1 / 1000 := by
    apply (div_le_iff₀ (sq_pos_of_pos hr0)).mpr
    nlinarith [sq_nonneg (r - 5)]
  unfold coreClockFactor
  constructor
  · linarith
  · exact sub_le_self _ (div_nonneg (sq_nonneg _) (sq_nonneg _))

theorem coreBootstrap_coupling_nonneg {k u v w : ℝ} (hk : 6 ≤ k) (hv : 1 ≤ v)
    (hu : 0 ≤ u ∧ u ≤ (1 / 10000) / k) (hw : 0 ≤ w) : 0 ≤ coupling u v w := by
  have hu' := coreBootstrap_wall_bound hk hu.2
  exact mul_nonneg hu.1 (by linarith)

/-- The strong-wall logarithmic numerator retains a negative term of order k. -/
theorem coreBootstrap_strong_numerator {k r u v w c : ℝ} (hk : 6 ≤ k)
    (hr : 99 / 100 * k ≤ r) (hv : v ≤ r) (hc : -1 ≤ c)
    (hu : 0 ≤ u ∧ u ≤ (1 / 10000) / k) (hw : 0 ≤ w ∧ w ≤ (1 / 10000) / k) :
    -r / 2 - c + (v / r) * w + (u ^ 2 - w ^ 2) / (2 * r) ≤ -3 * k / 10 := by
  have hr0 : 0 < r := by linarith
  have hu' := coreBootstrap_wall_bound hk hu.2
  have hw' := coreBootstrap_wall_bound hk hw.2
  have hvw : v / r * w ≤ w := by
    have H := mul_le_mul_of_nonneg_right ((div_le_one hr0).mpr hv) hw.1
    simpa only [one_mul] using H
  have hu2 : u ^ 2 ≤ (1 / 60000 : ℝ) ^ 2 := (sq_le_sq₀ hu.1 (by norm_num)).mpr hu'
  have he : (u ^ 2 - w ^ 2) / (2 * r) ≤ 1 / 100 := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [sq_nonneg w]
  linarith

theorem coreBootstrap_strong_rate {k r u v w c : ℝ} (hk : 6 ≤ k)
    (hr : 99 / 100 * k ≤ r) (hv : v ≤ r) (hc : -1 ≤ c)
    (hu : 0 ≤ u ∧ u ≤ (1 / 10000) / k) (hw : 0 ≤ w ∧ w ≤ (1 / 10000) / k) :
    (-r / 2 - c + (v / r) * w + (u ^ 2 - w ^ 2) / (2 * r)) / coreClockFactor r u w ≤ -k / 4 := by
  have ha := coreBootstrap_strong_numerator hk hr hv hc hu hw
  obtain ⟨hdlo, hdhi⟩ := coreBootstrap_clock_bounds hk hr hu hw
  apply (div_le_iff₀ (show 0 < coreClockFactor r u w by linarith)).mpr
  nlinarith

end BianchiIX
