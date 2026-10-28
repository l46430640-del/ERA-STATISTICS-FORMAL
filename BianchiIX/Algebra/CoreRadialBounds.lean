import BianchiIX.Algebra.CoreBounds

noncomputable section

namespace BianchiIX

theorem coreBootstrap_radius_closed {k r : ℝ} (hk : 6 ≤ k) (hr : 0 ≤ r)
    (he : |r ^ 2 - k ^ 2| ≤ 1 / 8) : 99 / 100 * k ≤ r ∧ r ≤ 101 / 100 * k := by
  obtain ⟨hl, hu⟩ := abs_le.mp he
  constructor
  · by_contra! hlt
    have hs : r ^ 2 < (99 / 100 * k) ^ 2 := (sq_lt_sq₀ hr (by linarith)).mpr hlt
    nlinarith
  · by_contra! hgt
    have hs : (101 / 100 * k) ^ 2 < r ^ 2 := (sq_lt_sq₀ (by linarith) hr).mpr hgt
    nlinarith

theorem core_radial_numerator_bound {r u v w c : ℝ} (hr : 0 < r)
    (hu : 0 ≤ u) (hw : 0 ≤ w) (hC : 0 ≤ coupling u v w) (hc : |c| ≤ 1) :
    |-coupling u v w - c * (u - w) ^ 2 / r| ≤ u * v + u * w + u ^ 2 / r + w ^ 2 / r := by
  have hδ : (u - w) ^ 2 ≤ u ^ 2 + w ^ 2 := by nlinarith [mul_nonneg hu hw]
  have hprod : |c * (u - w) ^ 2 / r| ≤ (u - w) ^ 2 / r := by
    rw [abs_div, abs_mul, abs_of_nonneg (sq_nonneg (u - w)), abs_of_pos hr]
    exact div_le_div_of_nonneg_right (by nlinarith [sq_nonneg (u - w)]) hr.le
  calc
    |-coupling u v w - c * (u - w) ^ 2 / r| ≤ coupling u v w + |c * (u - w) ^ 2 / r| := by
      simpa only [abs_neg, abs_of_nonneg hC] using abs_sub (-coupling u v w) (c * (u - w) ^ 2 / r)
    _ ≤ coupling u v w + (u ^ 2 + w ^ 2) / r := by
      have H := hprod.trans (div_le_div_of_nonneg_right hδ hr.le)
      linarith
    _ ≤ u * v + u * w + u ^ 2 / r + w ^ 2 / r := by
      rw [add_div]
      unfold coupling
      nlinarith [sq_nonneg u]

theorem core_radial_velocity_bound {k r u v w c : ℝ} (hk : 6 ≤ k)
    (hr : 99 / 100 * k ≤ r) (hv : 1 ≤ v)
    (hu : 0 ≤ u ∧ u ≤ (1 / 10000) / k) (hw : 0 ≤ w ∧ w ≤ (1 / 10000) / k)
    (hc : |c| ≤ 1) :
    |(-coupling u v w - c * (u - w) ^ 2 / r) / coreClockFactor r u w| ≤
      (u * v + u * w + u ^ 2 / r + w ^ 2 / r) / (999 / 1000) := by
  have hr0 : 0 < r := by linarith
  have hd := (coreBootstrap_clock_bounds hk hr hu hw).1
  have hd0 : 0 < coreClockFactor r u w := by linarith
  have hC := coreBootstrap_coupling_nonneg hk hv hu hw.1
  have hnum := core_radial_numerator_bound hr0 hu.1 hw.1 hC hc
  rw [abs_div, abs_of_pos hd0]
  exact (div_le_div_of_nonneg_right hnum hd0.le).trans
    (div_le_div_of_nonneg_left ((abs_nonneg _).trans hnum) (by norm_num) hd)

theorem core_radius_budget {k u w : ℝ} (hk : 6 ≤ k)
    (hu : 0 ≤ u ∧ u ≤ (1 / 10000) / k) (hw : 0 ≤ w ∧ w ≤ (1 / 10000) / k) :
    (14 * u / k + 4 * u * w / k + 3 * u ^ 2 / k ^ 2 + 4 * w ^ 2 / k) / (999 / 1000) ≤
      16 / k * (u + w ^ 2) := by
  have hk0 : 0 < k := by linarith
  have hu' := coreBootstrap_wall_bound hk hu.2
  have hw' := coreBootstrap_wall_bound hk hw.2
  have huw : u * w ≤ u / 60000 := by nlinarith [mul_nonneg hu.1 (sub_nonneg.mpr hw')]
  have huu : u ^ 2 ≤ u / 60000 := by nlinarith [mul_nonneg hu.1 (sub_nonneg.mpr hu')]
  have huuk : u ^ 2 / k ≤ u / 60000 :=
    (div_le_self (sq_nonneg u) (by linarith : 1 ≤ k)).trans huu
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 999 / 1000)).mpr
  apply (mul_le_mul_iff_right₀ hk0).mp
  field_simp
  nlinarith [sq_nonneg w, mul_nonneg hu.1 (show 0 ≤ k - 6 by linarith),
    mul_nonneg (show 0 ≤ u / 60000 - u * w by linarith) hk0.le]

theorem core_radius_energy_improvement {k r u w : ℝ} (hk : 6 ≤ k)
    (hr : 0 ≤ r) (hrhi : r ≤ 101 / 100 * k)
    (hu : 0 ≤ u ∧ u ≤ (1 / 10000) / k) (hw : 0 ≤ w ∧ w ≤ (1 / 10000) / k)
    (hR : |r - k| ≤ 16 / k * (u + w ^ 2)) : |r ^ 2 - k ^ 2| < 1 / 16 := by
  have hk0 : 0 < k := by linarith
  have hu' := coreBootstrap_wall_bound hk hu.2
  have hw' := coreBootstrap_wall_bound hk hw.2
  have hw2 := (sq_le_sq₀ hw.1 (by norm_num : (0 : ℝ) ≤ 1 / 60000)).mpr hw'
  have hnonneg : 0 ≤ 16 / k * (u + w ^ 2) :=
    mul_nonneg (by positivity) (add_nonneg hu.1 (sq_nonneg w))
  calc
    |r ^ 2 - k ^ 2| = |r - k| * (r + k) := by
      rw [show r ^ 2 - k ^ 2 = (r - k) * (r + k) by ring, abs_mul, abs_of_nonneg (by linarith : 0 ≤ r + k)]
    _ ≤ (16 / k * (u + w ^ 2)) * (201 / 100 * k) :=
      mul_le_mul hR (by linarith) (by linarith) hnonneg
    _ = (804 / 25) * (u + w ^ 2) := by field_simp; ring
    _ < 1 / 16 := by nlinarith

end BianchiIX
